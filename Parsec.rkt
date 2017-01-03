#lang racket/base
; parser combinators.
; use (require (prefix-in parsec: "ParseC.rkt")).
; TODO: this version relies on racket's string lib heavily.
;       find the most efficient way as replacement.
(require racket/string)

(define (string-map f str)
  (list->string (for/list ([i str]) (f i))))
(define (string-filter f str)
  (list->string (filter f (string->list str))))
(define (string-member x str)
  (member x (string->list str)))
(define (string-take/drop f str)
  (define (internal f str c)
    (if (f (string-ref str 0)) (internal f (substring str 1) (+ c 1)) c))
  (let ([p (internal f str 0)]) (values (substring str 0 p) (substring str p))))

(define (as x) (λ (t) x))
(define (ignored x) '())
(define (same x) `(,x))
(define (exact x as)
  (λ (str)
    (if (string-prefix? str x)
        (list (string-replace str x "" #:all? #F)
              (as x))

        #F)))
(define zero ; the as param is a placeholder
  (λ (str) (list str '())))
(define (one x as)
  (λ (str)
    (cond ((= (string-length str) 0) #F)
          ((string-contains? x (substring str 0 1))
           (list (substring str 1) (as (substring str 0 1))))
          (else #F))))
(define (multi x as)
  (define (count x str n)
    (if (or (= (string-length str) 0)
            (not (string-contains? x (substring str 0 1))))
        n (count x (substring str 1) (+ 1 n))))
  (λ (str)
    (let ([countRes (count x str 0)])
      (if (= countRes 0) #F
          (list (substring str countRes)
                (as (substring str 0 countRes)))))))
(define (and_ a b)
  (λ (str)
    (let ([aRes (a str)])
      (if aRes
        (let ([bRes (b (car aRes))])
          (if bRes (list (car bRes) (append (cadr aRes) (cadr bRes))) #F))
        #F))))
(define-syntax _and
  (syntax-rules ()
    [(_) zero]
    [(_ a) a]
    [(_ a b ...) (and_ a (_and b ...))]))
(define (or_ a b)
  (λ (str) (if (a str) (a str) (b str))))
(define-syntax _or
  (syntax-rules ()
    [(_) zero]
    [(_ a) a]
    [(_ a b ...) (or_ a (_or b ...))]))
(define (one/s x) (one x ignored))
(define (exact/s x) (exact x ignored))
(define (multi/s x) (multi x ignored))
(define (one? x as) (or_ (one x as)  zero))
(define (multi? x as) (or_ (multi x as) zero))
(define (one?/s x) (one? x ignored))
(define (multi?/s x) (multi? x ignored))

(define lowercase_latin_alphabet "abcdefghijklmnopqrstuvwxyz")
(define uppercase_latin_alphabet "ABCDEFGHIJKLMNOPQRSTUVWXYZ")
(define newline_ch "\n\r")
(define (newline as)
  (_or (exact "\n" as)
       (exact "\n\r" as))) ; use this!
(define whitespace_ch " \t")
(define digits "0123456789")
(define print_symbol "`~!@#$%^&*()_+-={}[]:\";'<>?,./")
(define-syntax set_of_symbol
  (syntax-rules (is with excluded)
    [(_ is (a ...) with (b ...) excluded)
     (excludestr (string-append a ...) (string-append b ...))]
    [(_ is a with b excluded) (excludestr a b)]
    [(_ is (a ...)) (string-append a ...)]
    [(_ is a) a]))
(define (excludestr a b)
  (if (string=? b "") a
      (excludestr (string-filter (λ (t) (not (char=? (string-ref b 0) t))) a)
                  (substring b 1))))

; TODO: check if using lets will refine the performance.
(define (exact/n x as)
  (define (count x str n)
    (cond ((> (string-length x) (string-length str))
           (+ n (string-length str)))
          ((string-prefix? str x) n)
          (#T (count x (substring str 1) (+ 1 n)))))
  (λ (str)
    (let ([countRes (count x str 0)])
      (if (= countRes 0) #F
          (list (substring str countRes)
                (as (substring str 0 countRes)))))))
(define (one/n x as)
  (λ (str)
    (if (and (not (= (string-length str) 0))
             (not (string-contains? x (substring str 0 1))))
        (list (substring str 1)
              (as (substring str 0 1)))
        #F)))
(define (multi/n x as)
  (define (count x str n)
    (if (or (= (string-length str) 0)
            (string-contains? x (substring str 0 1)))
        n (count x (substring str 1) (+ 1 n))))
  (λ (str)
    (let ([countRes (count x str 0)])
      (if (= countRes 0) #F
          (list (substring str countRes)
                (as (substring str 0 countRes)))))))

(define (_optional x) (_or x zero))

(define (_combR x y)
  (list (car y) (append (cadr x) (cadr y))))
(define (_repeat pc count)
  (if (= count 1) pc
      (_and pc (_repeat pc (- count 1)))))
(define (_matchuntil pc)
  (λ (str)
    (let ([matchRes (pc str)])
      (if matchRes
          (_combR matchRes ((_matchuntil pc) (car matchRes)))
          (list str '())))))

(provide (all-defined-out))