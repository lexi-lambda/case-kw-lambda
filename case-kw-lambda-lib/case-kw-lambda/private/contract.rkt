#lang racket/base

;; This module implements `case-kw->`, which is like `case->` but for
;; `case-kw-lambda` procedures. Currently, the implementation is not
;; particularly efficient, but it gets the job done. (A cleverer
;; implementation could build a specialized projection using `case-kw->`
;; itself, but this implementation just uses `make-keyword-procedure`.)

(require (for-syntax racket/base
                     racket/list
                     racket/set)
         racket/contract
         (only-in racket/contract/private/guts
                  nth-argument-of
                  nth-case-of)
         racket/format
         racket/list
         racket/match
         racket/set
         racket/string
         syntax/parse/define
         "base.rkt")

(provide case-kw->)

;; -----------------------------------------------------------------------------
;; helper functions

(define (build-contract-name . args)
  (apply apply build-compound-type-name args))

(define (english-list vs)
  (match vs
    [(list a)        (~a a)]
    [(list a b)      (~a a " and " b)]
    [(list as ... b) (~a (string-join (map ~a as) ", ") ", and " b)]))

;; Checks whether a sorted list of unique keywords `as` is a subset
;; of a sorted list of keywords `bs` in linear time.
(define (keywords<? as bs)
  (match* {as bs}
    [{'() _} #t]
    [{_ '()} #f]
    [{(cons a as) (cons a bs)}
     (keywords<? as bs)]
    [{_ (cons _ bs)}
     (keywords<? as bs)]))

;; -----------------------------------------------------------------------------
;; subcontracts and subcontract projections

(define (coerce-subcontract ctc)
  (coerce-contract 'case-kw-> ctc))
(define (coerce-subcontracts ctcs)
  (map coerce-subcontract ctcs))

;; Represents a `->` subcontract of a `case-kw->` contract.
(struct case-kw-arrow-contract
  (pos-ctcs    ; (listof contract?)
   kws         ; (listof keyword?)
   kw-ctcs     ; (listof contract?)
   rest-ctc    ; (or/c contract? #f)
   range-ctcs) ; (or/c (listof contract?) #f)
  #:transparent)

(define (build-case-kw-arrow-contract pos-ctcs
                                      kws
                                      kw-ctcs
                                      rest-ctc
                                      range-ctcs)
  (case-kw-arrow-contract
   (coerce-subcontracts pos-ctcs)
   kws
   (coerce-subcontracts kw-ctcs)
   (and rest-ctc (coerce-subcontract rest-ctc))
   (and range-ctcs (coerce-subcontracts range-ctcs))))

;; Represents a `->*` subcontract of a `case-kw->` contract.
(struct case-kw-arrow*-contract
  (req-pos-ctcs ; (listof contract?)
   opt-pos-ctcs ; (listof contract?)
   req-kws      ; (listof keyword?)
   req-kw-ctcs  ; (listof contract?)
   opt-kws      ; (listof keyword?)
   opt-kw-ctcs  ; (listof contract?)
   rest-ctc     ; (or/c contract? #f)
   range-ctcs)  ; (or/c (listof contract?) #f)
  #:transparent)

(define (build-case-kw-arrow*-contract req-pos-ctcs
                                       opt-pos-ctcs
                                       req-kws
                                       req-kw-ctcs
                                       opt-kws
                                       opt-kw-ctcs
                                       rest-ctc
                                       range-ctcs)
  (if (and (null? opt-pos-ctcs)
           (null? opt-kws)
           (not rest-ctc))
      (build-case-kw-arrow-contract req-pos-ctcs
                                    req-kws
                                    req-kw-ctcs
                                    rest-ctc
                                    range-ctcs)
      (case-kw-arrow*-contract
       (coerce-subcontracts req-pos-ctcs)
       (coerce-subcontracts opt-pos-ctcs)
       req-kws
       (coerce-subcontracts req-kw-ctcs)
       opt-kws
       (coerce-subcontracts opt-kw-ctcs)
       (and rest-ctc (coerce-subcontract rest-ctc))
       (and range-ctcs (coerce-subcontracts range-ctcs)))))

;; Represents a built projection for a `case-kw->` subcontract.
(struct case-kw-arrow-proj
  (min-pos
   max-pos
   pos-projs
   req-kws
   all-kws
   kw-projs
   rest-proj
   range-proj)
  #:transparent)

;; Given a list of range contracts, builds a projection of the form
;;   f : (-> blame? (-> any/c neg-party? (-> any/c ... any)))
;; such that ((f blame) val neg-party) can be used as a result-wrapper-proc for
;; a chaperoned or impersonated procedure. The result is specialized to use a
;; more efficient strategy for the overwhelmingly common cases that only one or
;; two values are expected to be returned.
(define (build-range-proj ctcs case-idx)
  (define num-expected (length ctcs))
  (define (wrong-number blame neg-party val results)
    (bad-number-of-results blame #:missing-party neg-party val
                           num-expected results case-idx))

  (match (map contract-late-neg-projection ctcs)
    [(list proj)
     (λ (blame)
       (define val-proj (proj blame))
       (λ (val neg-party)
         (case-lambda
           [(result) (with-contract-continuation-mark (cons blame neg-party)
                       (val-proj result neg-party))]
           [results (wrong-number blame neg-party val results)])))]

    [(list proj1 proj2)
     (λ (blame)
       (define val-proj1 (proj1 blame))
       (define val-proj2 (proj2 blame))
       (λ (val neg-party)
         (case-lambda
           [(result1 result2) (with-contract-continuation-mark (cons blame neg-party)
                                (values (val-proj1 result1 neg-party)
                                        (val-proj2 result2 neg-party)))]
           [results (wrong-number blame neg-party val results)])))]

    [projs
     (λ (blame)
       (define val-projs (map (λ (proj) (proj blame)) projs))
       (λ (val neg-party)
         (λ results
           (with-contract-continuation-mark (cons blame neg-party)
             (if (= (length results) num-expected)
                 (apply values (map (λ (proj result) (proj result neg-party)) val-projs results))
                 (wrong-number blame neg-party val results))))))]))

;; Builds a late-neg projection for a single case of a `case-kw->` contract.
;;
;; (-> (or/c case-kw-arrow-contract? case-kw-arrow*-contract?)
;;     case-kw-arrow-proj?)
(define (build-case-proj case case-idx)
  (match case
    ;; `->` case
    [(case-kw-arrow-contract pos-ctcs kws kw-ctcs rest-ctc range-ctcs)
     (define num-args (length pos-ctcs))
     (case-kw-arrow-proj
      num-args
      (and (not rest-ctc) num-args)
      (map contract-late-neg-projection pos-ctcs)
      kws
      kws
      (map contract-late-neg-projection kw-ctcs)
      (and rest-ctc
           ; For `->` cases, normalize a `...` contract so it accepts a list of
           ; rest arguments, just like a `#:rest` contract in an `->*` case.
           (let ([elem-proj (contract-late-neg-projection rest-ctc)])
             (λ (blame)
               (define elem-val-proj (elem-proj blame))
               (λ (vals neg-party)
                 (for/list ([val (in-list vals)])
                   (elem-val-proj val neg-party))))))
      (and range-ctcs (build-range-proj range-ctcs case-idx)))]

    ;; `->*` case
    [(case-kw-arrow*-contract req-pos-ctcs opt-pos-ctcs
                              req-kws req-kw-ctcs opt-kws opt-kw-ctcs
                              rest-ctc range-ctcs)
     (define min-args (length req-pos-ctcs))
     (case-kw-arrow-proj
      min-args
      (and (not rest-ctc) (+ min-args (length opt-pos-ctcs)))
      (map contract-late-neg-projection (append req-pos-ctcs opt-pos-ctcs))
      req-kws
      (append req-kws opt-kws)
      (map contract-late-neg-projection (append req-kw-ctcs opt-kw-ctcs))
      (and rest-ctc (contract-late-neg-projection rest-ctc))
      (and range-ctcs (build-range-proj range-ctcs case-idx)))]))

;; Applies a projection for a single `case-kw->` subcontract to a
;; blame object.
(define (apply-case-proj case blame)
  (match case
    [(case-kw-arrow-proj min-pos max-pos pos-projs
                         req-kws all-kws kw-projs
                         rest-proj range-proj)
     (case-kw-arrow-proj
      min-pos
      max-pos
      (for/list ([proj (in-list pos-projs)]
                 [n (in-naturals 1)])
        (proj (blame-add-context blame (nth-argument-of n) #:swap? #t)))
      req-kws
      (sort all-kws keyword<?)
      (for/hasheq ([kw (in-list all-kws)]
                   [proj (in-list kw-projs)])
        (values kw (proj (blame-add-context blame (format "the ~a argument of" kw) #:swap? #t))))
      (and rest-proj
           (rest-proj (blame-add-context blame "the rest argument of" #:swap? #t)))
      (and range-proj
           (range-proj (blame-add-context blame "the range of"))))]))

;; -----------------------------------------------------------------------------
;; contract structure

(define (build-case-kw-contract-property build-contract-property
                                         wrap-procedure)
  (define (arity-mask-includes? sup sub)
    (eqv? sub (bitwise-and sub sup)))

  (define (build-first-order self)
    (define arity-mask (case-kw-contract-arity-mask self))
    (define req-kws (case-kw-contract-req-kws self))
    (define opt-kws (case-kw-contract-opt-kws self))
    (λ (val)
      (and (procedure? val)
           (arity-mask-includes? (procedure-arity-mask val) arity-mask)
           (let ()
             (define-values [v-req-kws-lst v-all-kws-lst] (procedure-keywords val))
             (define v-all-kws (and v-all-kws-lst (list->seteq v-all-kws-lst)))
             (and (for/and ([kw (in-list v-req-kws-lst)])
                    (set-member? req-kws kw))
                  (or (not v-all-kws)
                      (and (subset? req-kws v-all-kws)
                           (subset? opt-kws v-all-kws))))))))

  (build-contract-property
   #:name
   (λ (self)
     (define (range-ctcs->name ranges)
       (match ranges
         [#f 'any]
         [(list range) range]
         [_ (build-contract-name 'values ranges)]))

     (build-contract-name
      'case-kw->
      (for/list ([case (in-list (case-kw-contract-cases self))])
        (match case
          [(case-kw-arrow-contract pos-ctcs kws kw-ctcs rest-ctc range-ctcs)
           (build-contract-name
            '->
            (append pos-ctcs
                    (append-map list kws kw-ctcs)
                    (if rest-ctc (list rest-ctc '...) '())
                    (list (range-ctcs->name range-ctcs))))]

          [(case-kw-arrow*-contract req-pos-ctcs opt-pos-ctcs
                                    req-kws req-kw-ctcs opt-kws opt-kw-ctcs
                                    rest-ctc range-ctcs)
           (build-contract-name
            '->*
            (build-contract-name (append req-pos-ctcs (append-map list req-kws req-kw-ctcs)))
            (append (if (and (empty? opt-pos-ctcs) (hash-empty? opt-kws))
                        '()
                        (list (build-contract-name
                               (append opt-pos-ctcs (append-map list opt-kws opt-kw-ctcs)))))
                    (if rest-ctc (list '#:rest rest-ctc) '())
                    (list (range-ctcs->name range-ctcs))))]))))

   #:first-order build-first-order
   #:late-neg-projection
   (λ (self)
     (define first-order-passes? (build-first-order self))
     (define arity-mask (case-kw-contract-arity-mask self))
     (define req-kws (case-kw-contract-req-kws self))
     (define opt-kws (case-kw-contract-opt-kws self))

     (define case-ctcs (case-kw-contract-cases self))
     (define case-projs (for/list ([ctc (in-list case-ctcs)]
                                   [idx (in-naturals)])
                          (build-case-proj ctc idx)))

     (λ (blame)
       (define case-val-projs
         (for/list ([proj (in-list case-projs)]
                    [n (in-naturals 1)])
           (apply-case-proj proj (blame-add-context blame (nth-case-of n)))))

       (λ (val neg-party)
         (define (bail msg . args)
           (apply raise-blame-error blame val #:missing-party neg-party
                  (list 'expected msg 'given: "~e")
                  (append args (list val))))

         (unless (procedure? val)
           (bail "a procedure"))

         (unless (first-order-passes? val)
           (define val-arity-mask (procedure-arity-mask val))
           (define-values [val-req-kws-lst val-all-kws-lst] (procedure-keywords val))

           (for ([i (in-range (integer-length arity-mask))]
                 #:when (bitwise-bit-set? arity-mask i)
                 #:unless (bitwise-bit-set? val-arity-mask i))
             (bail "a procedure that accepts ~a argument~a" i (if (= i 1) "" "s")))

           (when (and (negative? arity-mask) (not (negative? val-arity-mask)))
             (bail "a procedure that accepts arbitrarily many arguments"))

           (for ([req-kw (in-list val-req-kws-lst)]
                 #:unless (set-member? req-kws req-kw))
             (bail "a procedure that does not require a ~a argument" req-kw))

           (when val-all-kws-lst
             (define v-all-kws (list->seteq val-all-kws-lst))
             (for ([kw (in-immutable-set req-kws)]
                   #:unless (set-member? v-all-kws kw))
               (bail "a procedure that accepts a ~a argument" kw))
             (for ([kw (in-immutable-set opt-kws)]
                   #:unless (set-member? v-all-kws kw))
               (bail "a procedure that accepts an optional ~a argument" kw))))

         (wrap-procedure
          val
          (make-keyword-procedure
           (λ (kws kw-args . pos-args)
             (with-contract-continuation-mark (cons blame neg-party)
               (define num-pos-args (length pos-args))
               (let loop ([cases case-val-projs])
                 (match cases
                   [(cons (case-kw-arrow-proj min-pos max-pos pos-projs
                                              req-kws all-kws kw-projs
                                              rest-proj range-proj)
                          cases)
                    (cond
                      [(and (>= num-pos-args min-pos)
                            (or rest-proj
                                (<= num-pos-args max-pos))
                            (keywords<? req-kws kws)
                            (keywords<? kws all-kws))

                       (define pos-args* (let loop ([projs pos-projs]
                                                    [args pos-args])
                                           (match* {projs args}
                                             [{(cons proj projs) (cons arg args)}
                                              (cons (proj arg neg-party) (loop projs args))]
                                             [{_ '()} '()]
                                             [{_ _} (rest-proj args)])))

                       (define args* (if (empty? kws)
                                         pos-args*
                                         (cons (for/list ([kw (in-list kws)]
                                                          [arg (in-list kw-args)])
                                                 ((hash-ref kw-projs kw) arg neg-party))
                                               pos-args*)))

                       (if range-proj
                           (apply values (range-proj val neg-party) args*)
                           (apply values args*))]
                      [else
                       (loop cases)])]
                   ['()
                    (raise-blame-error
                     (blame-swap blame) #:missing-party neg-party
                     (~a "no case matching " num-pos-args " by-position "
                         "argument" (if (= num-pos-args 1) "" "s")
                         (if (empty? kws) ""
                             (~a " and keyword" (if (= (length kws) 1) "" "s")
                                 " " (english-list kws)))))])))))
          impersonator-prop:contracted self
          impersonator-prop:blame (cons blame neg-party)))))))

(struct case-kw-contract (cases arity-mask req-kws opt-kws)
  #:property prop:custom-write contract-custom-write-property-proc)
(struct chaperone-case-kw-contract case-kw-contract ()
  #:property prop:chaperone-contract
  (build-case-kw-contract-property build-chaperone-contract-property
                                   chaperone-procedure))
(struct impersonator-case-kw-contract case-kw-contract ()
  #:property prop:contract
  (build-case-kw-contract-property build-contract-property
                                   impersonate-procedure))

(define (build-case-kw-contract cases arity-mask req-kws opt-kws)
  ((if (for/and ([case (in-list cases)])
         (match case
           [(case-kw-arrow-contract pos-ctcs _ kw-ctcs rest-ctc range-ctcs)
            (and (andmap chaperone-contract? pos-ctcs)
                 (andmap chaperone-contract? kw-ctcs)
                 (or (not rest-ctc) (chaperone-contract? rest-ctc))
                 (or (not range-ctcs) (andmap chaperone-contract? range-ctcs)))]
           [(case-kw-arrow*-contract req-pos-ctcs opt-pos-ctcs
                                     _ req-kw-ctcs _ opt-kw-ctcs
                                     rest-ctc range-ctcs)
            (and (andmap chaperone-contract? req-pos-ctcs)
                 (andmap chaperone-contract? opt-pos-ctcs)
                 (andmap chaperone-contract? req-kw-ctcs)
                 (andmap chaperone-contract? opt-kw-ctcs)
                 (or (not rest-ctc) (chaperone-contract? rest-ctc))
                 (or (not range-ctcs) (andmap chaperone-contract? range-ctcs)))]))
       chaperone-case-kw-contract
       impersonator-case-kw-contract)
   cases arity-mask req-kws opt-kws))

;; -----------------------------------------------------------------------------
;; contract form

(begin-for-syntax
  (define-syntax-class ctc
    #:description "a contract expression"
    #:opaque
    #:attributes [ctc]
    #:commit
    (pattern {~and ctc:expr {~not {~literal ...}}}))

  (define-splicing-syntax-class arg-ctc
    #:description #f
    #:attributes [kw ctc]
    #:commit
    (pattern {~seq kw:keyword ~! :ctc})
    (pattern :ctc #:attr kw #f))

  (define-splicing-syntax-class arg-ctcs
    #:description #f
    #:attributes [{pos-ctc 1} {kw 1} {kw-ctc 1}]
    (pattern {~seq arg:arg-ctc ...}
      #:do [(define-values [pos-ctcs kws kw-ctcs]
              (for/fold ([pos-ctcs '()]
                         [kws '()]
                         [kw-ctcs '()])
                        ([kw (in-list (attribute arg.kw))]
                         [ctc (in-list (attribute arg.ctc))])
                (if kw
                    (values pos-ctcs (cons kw kws) (cons ctc kw-ctcs))
                    (values (cons ctc pos-ctcs) kws kw-ctcs))))]
      #:attr {pos-ctc 1} (reverse pos-ctcs)
      #:do [(define kws+ctcs (sort (map cons kws kw-ctcs)
                                   keyword<?
                                   #:key (λ (v) (syntax-e (car v)))))]
      #:attr {kw 1} (map car kws+ctcs)
      #:attr {kw-ctc 1} (map cdr kws+ctcs)))

  (define-syntax-class range-ctc
    #:description "a range contract"
    #:attributes [{ctc 1}]
    #:commit
    #:literals [any values]
    (pattern any #:attr {ctc 1} #f)
    (pattern (values ~! :ctc ...))
    (pattern e:ctc
      #:attr {ctc 1} (list #'e.ctc)))

  (define-syntax-class arrow-ctc
    #:description "an arrow contract"
    #:attributes [struct-e arity-mask req-kws opt-kws]
    #:commit
    #:literals [-> ->*]

    (pattern (-> ~! doms:arg-ctcs
                 {~optional {~seq rest:ctc {~literal ...}}}
                 range:range-ctc)
      #:fail-when (check-duplicates (attribute doms.kw) eq? #:key syntax-e) "duplicate keyword"

      #:attr struct-e
      #'(build-case-kw-arrow-contract
         (list doms.pos-ctc ...)
         (list 'doms.kw ...)
         (list doms.kw-ctc ...)
         {~? rest.ctc #f}
         {~? (list range.ctc ...) #f})

      #:attr arity-mask (make-arity-mask #:req (length (attribute doms.pos-ctc))
                                         #:opt 0
                                         #:rest? (attribute rest))
      #:attr req-kws (list->seteq (map syntax-e (attribute doms.kw)))
      #:attr opt-kws (seteq))

    (pattern (->* ~! [req-doms:arg-ctcs]
                  {~optional [opt-doms:arg-ctcs]}
                  {~optional {~seq #:rest ~! rest:ctc}}
                  range:range-ctc)
      #:fail-when (check-duplicates (append (attribute req-doms.kw)
                                            (or (attribute opt-doms.kw) '()))
                                    eq? #:key syntax-e)
      "duplicate keyword"

      #:attr struct-e
      #'(build-case-kw-arrow*-contract
         (list req-doms.pos-ctc ...)
         (list {~? {~@ opt-doms.pos-ctc ...}})
         (list 'req-doms.kw ...)
         (list req-doms.kw-ctc ...)
         (list {~? {~@ 'opt-doms.kw ...}})
         (list {~? {~@ opt-doms.kw-ctc ...}})
         {~? rest.ctc #f}
         {~? (list range.ctc ...) #f})

      #:attr arity-mask (make-arity-mask #:req (length (attribute req-doms.pos-ctc))
                                         #:opt (length (or (attribute opt-doms.pos-ctc) '()))
                                         #:rest? (attribute rest))
      #:attr req-kws (list->seteq (map syntax-e (attribute req-doms.kw)))
      #:attr opt-kws (list->seteq (map syntax-e (or (attribute opt-doms.kw) '()))))))

(define-syntax-parser case-kw->
  #:track-literals
  [(_ case:arrow-ctc ...)

   (define req-kws (if (empty? (attribute case.req-kws))
                       (seteq)
                       (apply set-intersect (attribute case.req-kws))))
   (define all-kws (apply set-union (seteq)
                          (append (attribute case.req-kws)
                                  (attribute case.opt-kws))))
   (define opt-kws (set-subtract all-kws req-kws))

   (define/syntax-parse [req-kw ...] (set->list req-kws))
   (define/syntax-parse [opt-kw ...] (set->list opt-kws))

   #`(build-case-kw-contract
      (list case.struct-e ...)
      #,(apply bitwise-ior (attribute case.arity-mask))
      (seteq 'req-kw ...)
      (seteq 'opt-kw ...))])
