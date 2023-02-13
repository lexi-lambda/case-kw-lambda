#lang racket/base

(require (for-syntax racket/base
                     racket/list
                     racket/set
                     racket/syntax
                     syntax/name)
         racket/match
         syntax/parse/define)

(provide (for-syntax make-arity-mask)
         case-kw-lambda)

#| Note [Compiling case-kw-lambda]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
From an implementation perspective, `case-kw-lambda` is essentially a
specialized pattern matcher, and the inclusion of both keywords and
optional arguments makes efficiently selecting the right case nontrivial
in general. Therefore, we usually compile `case-kw-lambda` to a
combination of `lambda` and `match`, since `match` implements various
pattern-matching optimizations; see Note [Compiling to `match`] for the
full details.

However, in general, expanding to `match` is unnecessary. To avoid
unnecessary overhead (at both compile-time and runtime), we detect
certain special cases and generate simpler code. The simplest of these
is obviously the situation where there are no optional or keyword
arguments at all, in which case we can just expand to `case-lambda`
directly. However, we also expand to `case-lambda` in a slightly less
direct way if there are optional arguments but no keywords; see
Note [Compilation without keywords] for the details.

Note [Preserve exact argument order]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We must take care to preserve the exact order in which formal arguments
are provided, even for keyword arguments, because the order in which
the arguments appear affects which bindings are in scope in default
value expressions. That is, these two expressions are different:

    (λ (#:x x #:y [y x]) y)
    (λ (#:y [y x] #:x x) y)

In the first expression, the default value of `y` is the value of the
`x` keyword argument, but in the second expression, it is the value of
whatever `x` is in the enclosing scope. This unfortunately means that
we cannot eagerly partition the arguments into four separate lists
based on whether they are required/optional and positional/keyword,
since that would erase information about their relative positions. |#

;; -----------------------------------------------------------------------------
;; parsing

(begin-for-syntax
  (struct parsed-formal
    (kw       ; (or/c (syntax/c keyword?) #f)
     id       ; identifier?
     default) ; (or/c syntax? #f)
    #:transparent)

  (define (parsed-formal-required? pf)
    (not (parsed-formal-default pf)))

  (struct parsed-case
    (src-stx ; syntax?
     formals ; (listof parsed-formal?) -- see Note [Preserve exact argument order]
     rest-id ; (or/c syntax? #f)
     body)   ; (non-empty-listof? syntax?)
    #:transparent)

  (define-syntax-class opt-formal
    #:description "identifier with default"
    #:attributes [id default]
    #:commit
    (pattern [id:id default:expr]))

  (define-splicing-syntax-class (formal #:pos-req? pos-req?)
    #:description "argument"
    #:attributes [parsed]
    #:commit
    (pattern {~and {~fail #:unless pos-req?}
                   id:id}
      #:attr parsed (parsed-formal #f #'id #f))
    (pattern {~and {~fail #:when pos-req?}
                   :opt-formal}
      #:attr parsed (parsed-formal #f #'id #'default))
    (pattern {~seq kw:keyword id:id}
      #:attr parsed (parsed-formal #'kw #'id #f))
    (pattern {~seq kw:keyword :opt-formal}
      #:attr parsed (parsed-formal #'kw #'id #'default)))

  (define-syntax-class formals
    #:description "argument sequence"
    #:attributes [{parsed 1} rest-id]
    #:commit
    (pattern ({~var arg/pos-req (formal #:pos-req? #t)} ...
              {~var arg/pos-opt (formal #:pos-req? #f)} ...
              . {~or* rest-id:id ()})

      #:attr {parsed 1} (append (attribute arg/pos-req.parsed)
                                (attribute arg/pos-opt.parsed))

      #:fail-when (check-duplicate-identifier
                   (append (map parsed-formal-id (attribute parsed))
                           (if (attribute rest-id)
                               (list #'rest-id)
                               '())))
                  "duplicate argument name"
      #:fail-when (check-duplicates
                   (filter-map parsed-formal-kw (attribute parsed))
                   eq? #:key syntax-e)
                  "duplicate keyword for argument"))

  (define-syntax-class case
    #:description "kw lambda case"
    #:attributes [parsed]
    #:commit
    (pattern [formals:formals body ...+]
      #:attr parsed (parsed-case this-syntax
                                 (attribute formals.parsed)
                                 (attribute formals.rest-id)
                                 (attribute body))))

  (define (parsed-formal->syntaxes pf)
    (define base-f (if (parsed-formal-default pf)
                       #`[#,(parsed-formal-id pf)
                          #,(parsed-formal-default pf)]
                       (parsed-formal-id pf)))
    (if (parsed-formal-kw pf)
        (list (parsed-formal-kw pf) base-f)
        (list base-f)))

  (define (parsed-formals->syntax pfs rest-id)
    #`[#,@(append-map parsed-formal->syntaxes pfs)
       . #,(or rest-id '())]))

#| -----------------------------------------------------------------------------
Note [Compilation without keywords]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
When there are no keyword arguments provided to `case-kw-lambda`, we
can efficiently expand to `case-lambda`. Cases without optional
arguments are already valid `case-lambda` clauses, so they can be
compiled unchanged, but cases with optional arguments need a little
more work. To illustrate our strategy, consider the following clause:

    [(a b [c e1] [d e2]) body]

Since this clause supports 2, 3, or 4 arguments, we need to generate 3
`case-lambda` clauses, one for each supported arity. We lift the body
into a `let`-bound `lambda`, which allows each case to just pass its
arguments along:

    (let ([tmp (lambda (a b [c e1] [d e2]) body)])
      (case-lambda
        [(a b) (tmp a b)]
        [(a b c) (tmp a b c)]
        [(a b c d) (tmp a b c d)]))

This conveniently allows us to rely on `lambda` to handle supplying
default values for any optional arguments. |#

;; Builds a `case-lambda` expression for a set of cases that include optional
;; arguments, but no keywords; see Note [Compilation without keywords].
(define-for-syntax (build-case-opt-lambda src-stx inferred-name cases)
  (define-values [fn-binds simple-cases]
    (for/foldr ([fn-binds '()]
                [simple-cases '()])
               ([case (in-list cases)])
      (define case-stx (parsed-case-src-stx case))
      (define formals (parsed-case-formals case))
      (define rest-id (parsed-case-rest-id case))
      (define body (parsed-case-body case))

      (define-values [req-ids opt-ids]
        (for/foldr ([req-ids '()] [opt-ids '()])
                   ([formal (in-list formals)])
          (define id (parsed-formal-id formal))
          (if (parsed-formal-default formal)
              (values req-ids (cons id opt-ids))
              (values (cons id req-ids) opt-ids))))

      (cond
        ;; If there are no optional arguments, we can just generate
        ;; a `case-lambda` clause directly.
        [(null? opt-ids)
         (values fn-binds (cons case-stx simple-cases))]
        [else
         (define fn-id (generate-temporary inferred-name))
         (define fn-bind #`[#,fn-id
                            #,(syntax-property
                               (quasisyntax/loc case-stx
                                 (lambda . #,case-stx))
                               'inferred-name
                               inferred-name)])

         (values
          (cons fn-bind fn-binds)
          (cond
            ;; If there’s a rest argument, we can generate a single `case-lambda`
            ;; clause, since we’re just going to call `apply` anyway.
            [rest-id
             (cons (quasisyntax/loc case-stx
                     [(#,@req-ids . #,rest-id)
                      #,(quasisyntax/loc case-stx
                          (apply #,fn-id #,@req-ids #,rest-id))])
                   simple-cases)]

            ;; Otherwise, generate a `case-lambda` clause for every possible arity.
            [else
             (for/foldr ([simple-cases simple-cases])
                        ([i (in-range (add1 (length opt-ids)))])
               (define opt-ids* (take opt-ids i))
               (cons (quasisyntax/loc case-stx
                       [(#,@req-ids #,@opt-ids*)
                        #,(quasisyntax/loc case-stx
                            (#,fn-id #,@req-ids #,@opt-ids*))])
                     simple-cases))]))])))

  ;; Put the pieces together.
  #`(let #,fn-binds
      #,(syntax-property
         (quasisyntax/loc src-stx
           (case-lambda #,@simple-cases))
         'inferred-name
         inferred-name)))

#| -----------------------------------------------------------------------------
Note [Compiling to `match`]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
If none of the special case shortcuts apply, we compile `case-kw-lambda`
to a `lambda` that wraps a use of `match*`. The `lambda` form must be
able to accept every possible argument combination, so the required
arguments to the `lambda` are the intersection of the required arguments
for each case, and the optional arguments are the union of all the other
arguments. For example, if we have

    (case-kw-lambda
     [(a b #:x [x #f]) e1]
     [(a #:x x #:y y)  e2])

then we would generate a lambda expression of the form

    (lambda (a
             [b unsupplied-case-kw-arg]
             #:x [x unsupplied-case-kw-arg]
             #:y [y unsupplied-case-kw-arg])
      ....)

since the only argument required in both cases is `a`. Now, in the body,
we need to determine which case matched (if any). Notably, we only need
to match on the presence or absence of each optional argument. Essentially,
we want to compile the above example to something like this:

    (match*/supplied {b x y}
      [{#t _  #f} (let* opt-binds1 e1)]
      [{#f #t #t} (let* opt-binds2 e2)])

This hypothetical `match*/supplied` form is easily implemented via
`match*`, which handles efficient selection of the right case.

If any of the cases accepts a rest argument, the protocol is slightly
different. The outer `lambda` must be able to accept any number of
positional arguments anyway, so we don’t bother generating *any* optional
positional arguments, just a rest argument. For example, if we have

    (case-kw-lambda
     [([a #f] #:x x) e1]
     [([a #f] . r)   e2])

then we’ll generate a `lambda` of the following form:

    (lambda (#:x [x unsupplied-case-kw-arg] . r) ....)

Note that we don’t bother to generate a separate optional `a` argument,
even though it appears in both cases. In theory, we could do so, but
it’s not clear that it would be worthwhile, especially given the
possibility of expressions like this one:

    (case-kw-lambda
     [([a #f]) e1]
     [r        e2])

In this case, should we generate a separate optional argument or not?
Whichever we choose, one of the cases will have to either unpack or
repack the first argument. So we just handle this uniformly for now. |#

(define unsupplied-case-kw-arg (gensym 'unsupplied-case-kw-arg))
(begin-for-syntax
  (define unsupplied-arg-pat #'(== unsupplied-case-kw-arg eq?))
  (define supplied-arg-pat #`(not #,unsupplied-arg-pat)))

(define (raise-no-cases-matched-error who args kws kw-args)
  (define kws+args (sort (map cons kws kw-args) keyword<? #:key car))
  (raise (exn:fail:contract:arity
          (apply string-append
                 who ": arity mismatch;\n"
                 " no case matching the given arguments\n"
                 "  arguments...:"
                 (append (for/list ([arg (in-list args)]
                                    #:break (eq? arg unsupplied-case-kw-arg))
                           (format "\n   ~e" arg))
                         (for/list ([kw+arg (in-list kws+args)]
                                    #:unless (eq? (cdr kw+arg) unsupplied-case-kw-arg))
                           (format "\n   ~a ~e" (car kw+arg) (cdr kw+arg)))))
          (current-continuation-marks))))

(begin-for-syntax
  (define (vector->list* vec [start 0] [end (vector-length vec)])
    (for/foldr ([lst '()]) ([v (in-vector vec start end)]) (cons v lst)))

  (define (make-arity-mask #:req req-args #:opt opt-args #:rest? rest?)
    (arithmetic-shift (if rest?
                          -1
                          (bitwise-not (arithmetic-shift -1 (add1 opt-args))))
                      req-args))

  (struct case-arity
    (req-pos ; exact-nonnegative-integer?
     opt-pos ; exact-nonnegative-integer?
     req-kws ; (set/c keyword?)
     opt-kws ; (set/c keyword?)
     rest?)  ; boolean?
    #:transparent)

  (define (case-arity-mask a)
    (make-arity-mask #:req (case-arity-req-pos a)
                     #:opt (case-arity-opt-pos a)
                     #:rest? (case-arity-rest? a)))

  ;; parsed-case? -> case-arity?
  (define (compute-case-arity case)
    (for/fold ([req-pos 0]
               [opt-pos 0]
               [req-kws (seteq)]
               [opt-kws (seteq)]
               #:result (case-arity req-pos
                                    opt-pos
                                    req-kws
                                    opt-kws
                                    (and (parsed-case-rest-id case) #t)))
              ([formal (in-list (parsed-case-formals case))])
      (define kw-stx (parsed-formal-kw formal))
      (cond
        [kw-stx
         (define kw (syntax-e kw-stx))
         (if (parsed-formal-required? formal)
             (values req-pos opt-pos (set-add req-kws kw) opt-kws)
             (values req-pos opt-pos req-kws (set-add opt-kws kw)))]
        [else
         (if (parsed-formal-required? formal)
             (values (add1 req-pos) opt-pos req-kws opt-kws)
             (values req-pos (add1 opt-pos) req-kws opt-kws))]))))

;; Builds a `lambda` expression for the given parsed cases. We defer
;; to `match*` to implement most of the case-matching logic, since it
;; implements various pattern-matching optimizations.
(define-for-syntax (build-case-kw-lambda src-stx inferred-name cases)
  ;; (listof parsed-formal?) -> (hash/c keyword? parsed-formal?)
  (define (collect-kw-formals formals)
    (for/hasheq ([formal (in-list formals)]
                 #:when (parsed-formal-kw formal))
      (values (syntax-e (parsed-formal-kw formal)) formal)))

  (define (build-opt-pos-formals ids)
    (for/list ([id (in-list ids)])
      #`[#,id unsupplied-case-kw-arg]))

  (define case-arities (map compute-case-arity cases))

  ;; Compute the overall function’s arity.
  (define-values
    [min-pos     ; the minimum number of required positional arguments
     max-pos     ; the maximum number of accepted positional arguments
                 ;  (+inf.0 if any cases have a rest argument)
     req-kws     ; the set of keywords that are required by all cases
     all-kws     ; the set of keywords that are accepted by any case
     arity-mask] ; the most precise arity mask possible for this function
    (for/fold ([min-pos #f]
               [max-pos 0]
               [req-kws #f]
               [all-kws (seteq)]
               [arity-mask 0])
              ([arity (in-list case-arities)])
      (values
       (if min-pos
           (min min-pos (case-arity-req-pos arity))
           (case-arity-req-pos arity))
       (max max-pos (if (case-arity-rest? arity)
                        +inf.0
                        (+ (case-arity-req-pos arity)
                           (case-arity-opt-pos arity))))
       (if req-kws
           (set-intersect req-kws (case-arity-req-kws arity))
           (case-arity-req-kws arity))
       (set-union all-kws (case-arity-req-kws arity) (case-arity-opt-kws arity))
       (bitwise-ior arity-mask (make-arity-mask #:req (case-arity-req-pos arity)
                                                #:opt (case-arity-opt-pos arity)
                                                #:rest? (case-arity-rest? arity))))))

  (define any-rest? (eqv? max-pos +inf.0))
  (define opt-pos (if any-rest? 0 (- max-pos min-pos)))
  (define opt-kws (set-subtract all-kws req-kws))
  (define all-kw-lst (sort (set->list all-kws) keyword<?))
  (define req-kw-lst (filter (λ (kw) (set-member? req-kws kw)) all-kw-lst))
  (define opt-kw-lst (filter (λ (kw) (set-member? opt-kws kw)) all-kw-lst))

  (define pos-ids (build-vector (if any-rest? min-pos max-pos) generate-temporary))
  (define kw-ids (for/hasheq ([kw (in-immutable-set all-kws)])
                   (values kw (generate-temporary kw))))
  (define rest-id (and any-rest? (generate-temporary 'rest)))

  ;; Generate a `match*` clause for each case; see Note [Compiling to `match`]
  ;; for the general strategy.
  (define match-clauses
    (for/list ([case (in-list cases)]
               [arity (in-list case-arities)])
      (define formals (parsed-case-formals case))
      (define case-min-opts (- (case-arity-req-pos arity) min-pos))
      (define case-max-opts (+ case-min-opts (case-arity-opt-pos arity)))
      (define kw-formals (collect-kw-formals formals))
      (define case-rest? (case-arity-rest? arity))

      (define kw-pats
        (for/list ([kw (in-list opt-kw-lst)])
          (define formal (hash-ref kw-formals kw #f))
          (cond
            [(set-member? (case-arity-req-kws arity) kw)
             supplied-arg-pat]
            [(set-member? (case-arity-opt-kws arity) kw)
             #'_]
            [else
             unsupplied-arg-pat])))

      (define (build-arg-binds get-pos-tmp-id)
        (for/fold ([i 0]
                   [arg-binds '()]
                   #:result (reverse arg-binds))
                  ([formal (in-list formals)])
          (define kw-stx (parsed-formal-kw formal))
          (define tmp-id (if kw-stx
                             (hash-ref kw-ids (syntax-e kw-stx))
                             (get-pos-tmp-id i)))
          (define arg-bind
            #`[#,(parsed-formal-id formal)
               #,(if (parsed-formal-required? formal)
                     tmp-id
                     #`(if (eq? #,tmp-id unsupplied-case-kw-arg)
                           #,(parsed-formal-default formal)
                           #,tmp-id))])
          (values (if kw-stx i (add1 i))
                  (cons arg-bind arg-binds))))

      (cond
        [any-rest?
         (define extra-pos-ids (build-vector case-max-opts generate-temporaries))
         (define extra-req-pos-ids (vector->list* extra-pos-ids 0 case-min-opts))
         (define opt-pos-ids (vector->list* extra-pos-ids case-min-opts))
         (define (get-pos-tmp-id i)
           (if (< i min-pos)
               (vector-ref pos-ids i)
               (vector-ref extra-pos-ids (- i min-pos))))

         (define base-rest-pat
           (if case-rest?
               rest-id
               #`(and rest-id
                      ;; Ensure there are not too many arguments.
                      (not (list* #,@(make-list (add1 (case-arity-opt-pos arity)) #'_) _)))))
         (define rest-pat
           #`(list* #,@extra-req-pos-ids #,base-rest-pat))

         #`[{#,@kw-pats #,rest-pat}
            (apply #,(quasisyntax/loc (parsed-case-src-stx case)
                       (lambda (#,@(build-opt-pos-formals opt-pos-ids)
                                . #,(if case-rest? rest-id '()))
                         #,(quasisyntax/loc (parsed-case-src-stx case)
                             (let* (#,@(build-arg-binds get-pos-tmp-id)
                                    #,@(if case-rest?
                                           (list #`[#,(parsed-case-rest-id case) #,rest-id])
                                           '()))
                               #,@(parsed-case-body case)))))
                   #,rest-id)]]

        [else
         (define pos-pats (for/list ([i (in-range opt-pos)])
                            (cond
                              [(= i (sub1 case-min-opts)) supplied-arg-pat]
                              [(= i case-max-opts)        unsupplied-arg-pat]
                              [else                       #'_])))

         #`[{#,@kw-pats #,@pos-pats}
            #,(quasisyntax/loc (parsed-case-src-stx case)
                (let* #,(build-arg-binds (λ (i) (vector-ref pos-ids i)))
                  #,@(parsed-case-body case)))]])))

  (define opt-pos-ids (vector->list* pos-ids min-pos))
  (define name-str (if (identifier? inferred-name)
                       (symbol->string (syntax-e inferred-name))
                       (format "~a" inferred-name)))
  (define lambda-expr
    (quasisyntax/loc src-stx
      (lambda (#,@(vector->list* pos-ids 0 min-pos)
               #,@(build-opt-pos-formals opt-pos-ids)
               #,@(append* (for/list ([kw (in-list req-kw-lst)])
                             (list kw (hash-ref kw-ids kw))))
               #,@(append* (for/list ([kw (in-list opt-kw-lst)])
                             (list kw #`[#,(hash-ref kw-ids kw) unsupplied-case-kw-arg]))))

        (match* {#,@(for/list ([kw (in-list opt-kw-lst)])
                      (hash-ref kw-ids kw))
                 #,@(if any-rest?
                        (list rest-id)
                        opt-pos-ids)}
          #,@match-clauses
          [#,(make-list (+ (set-count opt-kws) (if any-rest? 1 opt-pos)) #'_)
           (raise-no-cases-matched-error
            '#,name-str
            #,(if any-rest?
                  #`(list* #,@(vector->list pos-ids) #,rest-id)
                  #`(list #,@(vector->list pos-ids)))
            '#,all-kw-lst
            (list #,@(for/list ([kw (in-list all-kw-lst)])
                       (hash-ref kw-ids kw))))]))))

  ; In many cases, our constructed lambda expression will inherently have
  ; the most specific arity it can be given, in which case we have no need
  ; to bother altering it. But in some situations, we can do better, such as
  ; in the following case:
  ;
  ;     (case-kw-lambda
  ;       [(a b)               1]
  ;       [(a b c d)           2]
  ;       [(a b c d e f #:g g) 3]
  ;
  ; We’ll generate a lambda expression like
  ;
  ;     (lambda (a b [c <u>] [d <u>] [e <u>] [f <u>] #:g [g <u>]) ....)
  ;
  ; and that lambda will be given an arity that expects anywhere between 2
  ; and 6 by-position arguments. However, no cases actually accept 3 or 5
  ; by-position arguments, so we want to explicitly reduce the arity.
  (define inherent-arity-mask (make-arity-mask #:req min-pos
                                               #:opt opt-pos
                                               #:rest? any-rest?))
  (if (eqv? arity-mask inherent-arity-mask)
      lambda-expr
      #`(procedure-reduce-keyword-arity-mask
         #,(syntax-property lambda-expr 'inferred-name inferred-name)
         '#,arity-mask
         '#,req-kw-lst
         '#,all-kw-lst)))

;; -----------------------------------------------------------------------------

(define-syntax-parser case-kw-lambda
  ; No cases: expand to ordinary `case-lambda`.
  [(_)
   (syntax/loc this-syntax
     (case-lambda))]

  ; Single case: expand to ordinary `lambda`.
  [(_ case:case)
   (syntax/loc this-syntax
     (lambda . case))]

  [(_ case:case ...+)
   (define cases (attribute case.parsed))
   (define any-kw? (for*/or ([case (in-list cases)]
                             [formal (in-list (parsed-case-formals case))])
                     (and (parsed-formal-kw formal) #t)))
   (define any-opt? (for*/or ([case (in-list cases)]
                              [formal (in-list (parsed-case-formals case))])
                      (not (parsed-formal-required? formal))))
   (cond
     ; No keywords or optional arguments: expand to ordinary `case-lambda`.
     [(and (not any-kw?) (not any-opt?))
      (syntax/loc this-syntax
        (case-lambda case ...))]
     [else
      (define inferred-name (syntax-local-infer-name this-syntax))
      (cond
        ; No keywords: expand to `case-lambda` via `build-case-opt-lambda`.
        [(not any-kw?)
         (build-case-opt-lambda this-syntax inferred-name cases)]
        ; Keywords: expand to `lambda` + `match*` via `build-case-kw-lambda`.
        [else
         (build-case-kw-lambda this-syntax inferred-name cases)])])])
