#lang racket/base

(require case-kw-lambda
         racket/contract
         rackunit)

(let ()
  (define f
    (contract
     (case-kw->
      (-> exact-integer? exact-integer?)
      (->* [#:f (-> symbol? string?)] [symbol?] string?))
     (case-kw-lambda
       [(x) x]
       [([v 'hello] #:f f) (f v)])
     'pos
     'neg))

  (check-equal? (f 10) 10)
  (check-equal? (f #:f symbol->string) "hello")
  (check-equal? (f 'other #:f symbol->string) "other")

  (let ()
    (define b (with-handlers ([exn:fail:contract:blame? exn:fail:contract:blame-object])
                (f 'not-an-integer)))
    (check-pred blame? b)
    (check-equal? (blame-positive b) 'neg)
    (check-equal? (blame-context b) '("the 1st argument of" "the 1st case of")))

  (let ()
    (define b (with-handlers ([exn:fail:contract:blame? exn:fail:contract:blame-object])
                (f #:f values)))
    (check-pred blame? b)
    (check-equal? (blame-positive b) 'neg)
    (check-equal? (blame-context b) '("the range of"
                                      "the #:f argument of"
                                      "the 2nd case of")))

  (let ()
    (define b (with-handlers ([exn:fail:contract:blame? exn:fail:contract:blame-object])
                (f "not a symbol" #:f symbol->string)))
    (check-pred blame? b)
    (check-equal? (blame-positive b) 'neg)
    (check-equal? (blame-context b) '("the 1st argument of" "the 2nd case of"))))

(check-equal? (contract-name (case-kw->
                              (->* [] [real? real?] any/c)
                              (->* [] [#:h real? #:w real?] any/c)))
              '(case-kw->
                (->* [] [real? real?] any/c)
                (->* [] [#:h real? #:w real?] any/c)))
