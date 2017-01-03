#lang racket/base
(require "Parsec.rkt")

; assembly.
;
; program = statements
; statements = statement
;            | statement statements
;            | comment
; statement = identifier :
;         0 | op0 Integer
;         1 | op1 Integer
;         2 | op2 Integer
;         3 | op3 Integer
;         4 | load Integer / identifier
;         5 | store Integer / identifier
;         6 | lit Integer
;         7 | rm
;         8 | jmp Integer / identifier
;         9 | jz Integer / identifier
;        10 | jnz Integer / identifier
;        11 | arg Integer
;        12 | retr Integer
;        13 | call Integer / identifier
;        14 | ret
;        15 | hlt
; comment = % [any-character-here]

(define whitespace? (multi?/s whitespace_ch))
(define whitespace/?
  (multi?/s (set_of_symbol is (whitespace_ch newline_ch))))
(define whitespace (multi/s whitespace_ch))
(define whitespace/ (multi/s whitespace_ch))

(define comment
  (_and (_optional (multi? whitespace_ch ignored))
        (exact "%" ignored)
        (exact/n "\n" ignored)
        (_optional (multi? newline_ch ignored))))
(define identifier
  (let* ([symbols1 (set_of_symbol is (uppercase_latin_alphabet
                                      lowercase_latin_alphabet
                                      "_"))]
         [symbols2 (set_of_symbol is (symbols1 digits))])
    (λ (str)
      (let ([result ((_and (one symbols1 same) (multi? symbols2 same)) str)])
        (if result
            `(,(car result) (,(apply string-append (cadr result))))
            #F)))))
(define (integer str)
  (define (preInteger str)
    (let ([result ((_and (one "123456789" same) (multi? digits same)) str)])
      (if result
          (list (car result) (list (apply string-append (cadr result))))
          #F)))
  (let ([result ((_or (exact "0" same)
                      (_and (_optional (one "+-" same))
                            preInteger)) str)])
    (if result
        `(,(car result)
          (,(string->number (apply string-append (cadr result)))))
        #F)))
(define (label str)
  (let ([result ((_and (multi? whitespace_ch ignored)
                       identifier (multi? whitespace_ch ignored)
                       (exact ":" ignored)
                       (multi? (string-append
                                whitespace_ch
                                newline_ch) ignored)) str)])
    (if result
        `(,(car result) ((LABEL ,(caadr result))))
        #F)))
; program = statements
; statements = statement
;            | statement statements
;            | comment
; statement = identifier :
;         0 | op0 Integer
;         1 | op1 Integer
;         2 | op2 Integer
;         3 | op3 Integer
;         4 | load Integer / identifier
;         5 | store Integer / identifier
;         6 | lit Integer
;         7 | rm
;         8 | jmp Integer / identifier
;         9 | jz Integer / identifier
;        10 | jnz Integer / identifier
;        11 | arg Integer
;        12 | retr Integer
;        13 | call Integer / identifier
;        14 | ret
;        15 | hlt
(define intOrID (_or integer identifier))
(define (mk0 str as)
  (_and (multi? whitespace_ch ignored)
        (exact str as)
        (multi? whitespace_ch ignored)))
(define (mkInt str as)
  (_and (multi? whitespace_ch ignored)
        (exact str as)
        (multi? whitespace_ch ignored)
        integer
        (multi? whitespace_ch ignored)))
(define (mkIntOrID str as)
  (_and (multi? whitespace_ch ignored)
        (exact str as)
        (multi? whitespace_ch ignored)
        (_or integer identifier)
        (multi? whitespace_ch ignored)))
(define op0 (mkInt "op0" (as '(OP0))))
(define op1 (mkInt "op1" (as '(OP1))))
(define op2 (mkInt "op2" (as '(OP2))))
(define op3 (mkInt "op3" (as '(OP3))))
(define load (mkIntOrID "load" (as '(LOAD))))
(define store (mkIntOrID "store" (as '(STORE))))
(define lit (mkInt "lit" (as '(LIT))))
(define rm (mk0 "rm" (as '(RM))))
(define jmp (mkIntOrID "jmp" (as '(JMP))))
(define jz (mkIntOrID "jz" (as '(JZ))))
(define jnz (mkIntOrID "jnz" (as '(JNZ))))
(define arg (mkInt "arg" (as '(ARG))))
(define retr (mkInt "retr" (as '(RETR))))
(define call (mkIntOrID "call" (as '(CALL))))
(define ret (mk0 "ret" (as '(RET))))
(define hlt (mk0 "hlt" (as '(HLT))))
(define statement
  (_and (_or label op0 op1 op2 op3 load store lit rm jmp
             jz jnz arg retr call ret hlt)
        (multi? (set_of_symbol is
                  (newline_ch whitespace_ch)) ignored)))
(define (statements str)
  ((_and statement
         (_optional statements)) str))
(define (addLabel name pos labelMap)
  (if (assoc name labelMap)
      (error "duplicated label name")
      `((,name . pos) . ,labelMap)))
(define (lookup name labelMap)
  (cdr (assoc name labelMap)))
(define (compile_ code pc labelMap)
  (cond ((null? code) '())
        ((list? (car code))
          (compile_ (cdr code) pc (addLabel (cadar code) pc labelMap)))
        (#T
         (case (car code)
           ((OP0)
            `(0 ,(cadr code) . ,(compile_ (cddr code) (+ pc 2) labelMap)))
           ((OP1)
            `(1 ,(cadr code) . ,(compile_ (cddr code) (+ pc 2) labelMap)))
           ((OP2)
            `(2 ,(cadr code) . ,(compile_ (cddr code) (+ pc 2) labelMap)))
           ((OP3)
            `(3 ,(cadr code) . ,(compile_ (cddr code) (+ pc 2) labelMap)))
           ((LOAD)
            `(4 ,(if (string? (cadr code))
                     (lookup (cadr code) labelMap)
                     (cadr code))
                . ,(compile_ (cddr code) (+ pc 2) labelMap)))
           ((STORE)
            `(5 ,(if (string? (cadr code))
                     (lookup (cadr code) labelMap)
                     (cadr code))
             . ,(compile_ (cddr code) (+ pc 2) labelMap)))
           ((LIT)
            `(6 ,(cadr code) . ,(compile_ (cddr code) (+ pc 2) labelMap)))
           ((RM) `(7 . ,(compile_ (cdr code) (+ pc 1) labelMap)))
           ((JMP)
            `(8 ,(if (string? (cadr code))
                     (lookup (cadr code) labelMap)
                     (cadr code))
                . ,(compile_ (cddr code) (+ pc 2) labelMap)))
           ((JZ)
            `(9 ,(if (string? (cadr code))
                     (lookup (cadr code) labelMap)
                     (cadr code))
                . ,(compile_ (cddr code) (+ pc 2) labelMap)))
           ((JNZ)
            `(10 ,(if (string? (cadr code))
                      (lookup (cadr code) labelMap)
                      (cadr code))
                 . ,(compile_ (cddr code) (+ pc 2) labelMap)))
           ((ARG)
            `(11 ,(cadr code) . ,(compile_ (cddr code) (+ pc 2) labelMap)))
           ((RETR)
            `(12 ,(cadr code) . ,(compile_ (cddr code) (+ pc 2) labelMap)))
           ((CALL)
            `(13 ,(if (string? (cadr code))
                      (lookup (cadr code) labelMap)
                      (cadr code))
                 . ,(compile_ (cddr code) (+ pc 2) labelMap)))
           ((RET) `(14 . ,(compile_ (cdr code) (+ pc 1) labelMap)))
           ((HLT) `(15 . ,(compile_ (cdr code) (+ pc 1) labelMap)))))))
(define (compile str)
  (let ([result (statements str)])
    (if result
        (list->vector (compile_ (cadr result) 0 '()))
        (error "compile failed. check your source code."))))