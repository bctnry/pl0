#lang racket/base
(provide run0)

(define (take l n)
  (define (take_ l n hold)
    (if (= n 0) (reverse hold) (take_ (cdr l) (- n 1) (cons (car l) hold))))
  (take_ l n '()))
(define (drop l n)
  (if (= n 0) l (drop (cdr l) (- n 1))))
(define run0
  ; literal stack | arg stack | call stack | pc
  ; Value : Integer | Boolean
  ; LStack : [Value]
  ; AStack : [Value]
  ; CStack : [(Integer, Integer)] ; argnum, pc
  ; PC : Integer
  ; op0 : Num -> LStack -> LStack :: Integer -> Integer
  ; op1 : Num -> LStack -> LStack :: Integer -> Boolean
  ; op2 : Num -> LStack -> LStack :: Boolean -> Boolean
  ; op3 : LStack -> LStack        :: Boolean -> Integer
  (let ([op0 (λ (n) (case n ((0) +) ((1) -) ((2) *) ((3) quotient)))]
        [op1 (λ (n) (case n ((0) =) ((1) <) ((2) >) ((3) (λ (n) (> n 0)))))]
        [op2 (λ (n) (case n ((0) (λ (a b) (and a b)))
                             ((1) (λ (a b) (or a b)))))]
        [jmpc (λ (n) (case n ((0) (λ (a) #T)) ((1) (λ (a) (= a 0)))))])
    (λ (code lst ast cst pc)
    ; Commands:
    ;     0 | op0 Integer
    ;     1 | op1 Integer
    ;     2 | op2 Integer
    ;     3 | op3 Integer
    ;     4 | load Integer 
    ;     5 | store Integer
    ;     6 | lit Integer
    ;     7 | rm
    ;     8 | jmp Integer
    ;     9 | jz Integer
    ;    10 | jnz Integer
    ;    11 | arg Integer
    ;    12 | retr Integer
    ;    13 | call Integer
    ;    14 | ret
    ;    15 | hlt
      (case (vector-ref code pc)
        ((0) (run0 code (cons ((op0 (vector-ref code (+ pc 1)))
                               (car lst) (cadr lst)) (cddr lst))
                   ast cst (+ pc 2)))
        ((1) (run0 code (cons ((op1 (vector-ref code (+ pc 1)))
                               (car lst) (cadr lst)) (cddr lst))
                   ast cst (+ pc 2)))
        ((2) (case (vector-ref code (+ pc 1))
              ((2) (run0 code (cons (not (car lst)) (cdr lst))
                         ast cst (+ pc 2)))
              ((0 1) (run0 code (cons ((op2 (vector-ref code (+ pc 1)))
                                       (car lst) (cadr lst)) (cddr lst))
                           ast cst (+ pc 2)))))
        ((3) (run0 code (cons (if (car lst) 1 0) (cdr lst)) ast cst (+ pc 1)))
        ((4) (run0 code (cons (vector-ref code (vector-ref code (+ pc 1))) lst)
                   ast cst (+ pc 2)))
        ((5) (run0 (begin0 code
                     (vector-set! code (vector-ref code (+ pc 1)) (car lst)))
                   (cdr lst) ast cst (+ pc 2)))
        ((6) (run0 code (cons (vector-ref code (+ pc 1)) lst) ast cst (+ pc 2)))
        ((7) (run0 code (cdr lst) ast cst (+ pc 1)))
        ((8) (run0 code lst ast cst (vector-ref code (+ pc 1))))
        ((9) (run0 code lst ast cst
                   (if (= (car lst) 0) (vector-ref code (+ pc 1)) (+ pc 2))))
        ((10) (run0 code lst ast cst
                    (if (not (= (car lst) 0))
                        (vector-ref code (+ pc 1)) (+ pc 2))))
        ((11) (let ([argn (vector-ref code (+ pc 1))])
                (run0 code (drop lst argn) (append (take lst argn) ast) cst
                      (+ pc 2))))
        ((12) (let ([argn (vector-ref code (+ pc 1))])
                (run0 code (append (take ast argn) lst)
                      (drop ast argn) cst (+ pc 2))))
        ((13) (run0 code lst ast (cons (+ pc 1) cst) (vector-ref code (+ pc 1))))
        ((14) (run0 code lst ast (cdr cst) (car cst)))
        ((15) (values code lst ast cst pc))))))
