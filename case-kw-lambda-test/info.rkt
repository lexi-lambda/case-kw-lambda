#lang info

(define version "1.0")

(define collection 'multi)

(define deps '("base"))
(define build-deps
  '(["case-kw-lambda-lib" #:version "1.0"]
    "rackunit-lib"))
