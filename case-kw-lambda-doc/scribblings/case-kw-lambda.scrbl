#lang scribble/manual

@(require (for-label case-kw-lambda
                     racket/base
                     racket/contract)
          scribble/example)

@title{@tt{case-kw-lambda}}
@author{@author+email["Alexis King" "lexi.lambda@gmail.com"]}
@margin-note{The source of this manual is available on @hyperlink["https://github.com/lexi-lambda/case-kw-lambda/blob/master/case-kw-lambda-doc/scribblings/case-kw-lambda.scrbl"]{GitHub.}}
@defmodule[case-kw-lambda]

@(define (reftech . pre-content)
   (apply tech pre-content #:doc '(lib "scribblings/reference/reference.scrbl")))

@(define make-case-kw-eval (make-eval-factory '(case-kw-lambda
                                                racket/contract)))
@(define-syntax-rule (case-kw-examples body ...)
   (examples #:eval (make-case-kw-eval) #:once body ...))

This package provides the @racket[case-kw-lambda] form, a variant of @racket[case-lambda] that has been extended to support keyword arguments and optional arguments like @racket[lambda]. Additionally, it provides the @racket[case-kw->] contract combinator, which extends @racket[case->] with support for keyword arguments and @racket[->*] subcontracts.

@defform[(case-kw-lambda
           [kw-formals body ...+] ...)
         #:grammar
         ([kw-formals (arg ...)
                      (arg ...+ . rest-id)
                      rest-id]
          [arg id
               [id default-expr]
               (code:line keyword id)
               (code:line keyword [id default-expr])])]{
Produces a procedure. Each @racket[[kw-formals body ...]] clause is analogous to a single @racket[lambda] procedure; applying the @racket[case-kw-lambda]-generated procedure is the same as applying a procedure that corresponds to one of the clauses---the first procedure that accepts the given arguments. If no corresponding procedure accepts the given arguments, an @racket[exn:fail:contract:arity] exception is raised.

Note that, unlike @racket[case-lambda], a @racket[case-kw-lambda] clause supports the full @racket[kw-formals] of @racket[lambda], including keyword and optional arguments.

@(case-kw-examples
  (define distance
    (case-kw-lambda
      [(dx dy)
       (distance #:dx dx #:dy dy)]
      [(#:dx dx #:dy dy)
       (sqrt (+ (expt dx 2) (expt dy 2)))]))
  (eval:check (distance 3 4) 5)
  (eval:check (distance #:dx 5 #:dy 12) 13)
  (eval:error (distance 8 #:dy 15)))}

@(define literal-ellipsis @racket[...])
@defform[#:literals [-> ->* values any]
         (case-kw-> arr-ctc ...)
         #:grammar
         ([arr-ctc (-> dom ... range)
                   (-> dom ... dom-expr ellipsis dom ... range)
                   (->* [dom ...] optional-doms rest range)]
          [dom dom-expr
               (code:line keyword dom-expr)]
          [optional-doms (code:line)
                         (code:line [dom ...])]
          [rest (code:line)
                (code:line #:rest rest-expr)]
          [range range-expr
                 (values range-expr ...)
                 any]
          [ellipsis #,literal-ellipsis])]{
Produces an contract intended to match @racket[case-kw-lambda]. Each @racket[arr-ctc] is a contract that governs a clause in the @racket[case-kw-lambda]; its grammar matches that of @racket[->] and @racket[->*].}
