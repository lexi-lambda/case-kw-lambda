#lang info

(define version "1.0")
(define license 'ISC)

(define collection 'multi)

(define deps
  '("base"
    "case-kw-lambda-doc"
    "case-kw-lambda-lib"))
(define build-deps '())

(define implies
  '("case-kw-lambda-doc"
    "case-kw-lambda-lib"))
