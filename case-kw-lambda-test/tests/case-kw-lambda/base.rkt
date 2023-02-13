#lang racket/base

(require case-kw-lambda
         rackunit)

(let ()
  (define empty-fn (case-kw-lambda))
  (check-equal? (object-name empty-fn) 'empty-fn)
  (check-equal? (procedure-arity empty-fn) '())
  (define-values [req-kws accepted-kws] (procedure-keywords empty-fn))
  (check-equal? req-kws '())
  (check-equal? accepted-kws '()))

(let ()
  (define single-fn
    (case-kw-lambda
      [(x [y 1] #:a a #:b [b 3])
       (list x y a b)]))

  (check-equal? (object-name single-fn) 'single-fn)
  (check-equal? (procedure-arity single-fn) '(1 2))
  (define-values [req-kws accepted-kws] (procedure-keywords single-fn))
  (check-equal? req-kws '(#:a))
  (check-equal? accepted-kws '(#:a #:b))

  (check-equal? (single-fn 0 #:a 2) '(0 1 2 3))
  (check-equal? (single-fn 'a 'b #:a 'c #:b 'd) '(a b c d)))

(let ()
  (define no-kws-fn
    (case-kw-lambda
      [() #f]
      [(a [b 1]) (list a b)]
      [(a b c d [e 4]) (list a b c d e)]))

  (check-equal? (object-name no-kws-fn) 'no-kws-fn)
  (check-equal? (procedure-arity no-kws-fn) '(0 1 2 4 5))
  (define-values [req-kws accepted-kws] (procedure-keywords no-kws-fn))
  (check-equal? req-kws '())
  (check-equal? accepted-kws '())

  (check-equal? (no-kws-fn) #f)
  (check-equal? (no-kws-fn 0) '(0 1))
  (check-equal? (no-kws-fn 'a 'b) '(a b))
  (check-equal? (no-kws-fn 0 1 2 3) '(0 1 2 3 4))
  (check-equal? (no-kws-fn 'a 'b 'c 'd 'e) '(a b c d e)))

(let ()
  (define kws-fn
    (case-kw-lambda
      [(a #:b b) (list a b)]
      [(a #:b b [c 2] #:d [d 3]) (list a b c d)]))

  (check-equal? (object-name kws-fn) 'kws-fn)
  (check-equal? (procedure-arity kws-fn) '(1 2))
  (define-values [req-kws accepted-kws] (procedure-keywords kws-fn))
  (check-equal? req-kws '(#:b))
  (check-equal? accepted-kws '(#:b #:d))

  (check-equal? (kws-fn 0 #:b 1) '(0 1))
  (check-equal? (kws-fn 0 #:b 1 2) '(0 1 2 3))
  (check-equal? (kws-fn 'a #:b 'b 'c #:d 'd) '(a b c d)))
