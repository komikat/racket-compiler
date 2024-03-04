#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require racket/match)
(require graph)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(require "interp.rkt")
(provide (all-defined-out))


(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x) (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Let x e body) (let [(x-uniq (gensym))]
                        (let [(new-uniq-pass (uniquify-exp (dict-set env x x-uniq)))]
                          (Let x-uniq (new-uniq-pass e) (new-uniq-pass body))))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : Lvar -> Lvar
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

(define (rco-exp env)
  (lambda (e)
    (match e
      [(Let x e body) (Let x ((rco-exp env) e) ((rco-exp env) body))]
      [(or (Int _) (Var _)) e]
      [(Prim 'read '()) (Prim 'read '())]
      [(Prim '- (list (or (Int _) (Var _)))) e]
      [(Prim (or '- '+) (list (or (Int _) (Var _)) (or (Var _) (Int _)))) e]
      [(Prim '- (list e2)) (let [(x ((rco-atom env) e2))] (Let x ((rco-exp env) e2) (Prim '- (list (Var x)))))]
      [(Prim op (list e1 e2)) #:when (and (or (Int? e1) (Var? e1)) (or (eq? op '-) (eq? op '+))) (let [(x ((rco-atom env) e2))] (Let x ((rco-exp env) e2) (Prim op (list e1 (Var x)))))]
      [(Prim op (list e1 e2)) #:when (and (or (Int? e2) (Var? e2)) (or (eq? op '-) (eq? op '+))) (let [(x ((rco-atom env) e1))] (Let x ((rco-exp env) e1) (Prim op (list (Var x) e2))))]
      [(Prim op (list e1 e2)) #:when (or (eq? op '-) (eq? op '+)) (let [(x ((rco-atom env) e1))] (let [(y ((rco-atom env) e2))] (Let x ((rco-exp env) e1) (Let y ((rco-exp env) e2)) (Prim op (list (Var x) (Var y))))))])))
      
(define (rco-atom env)
  (lambda (e)
    (let [(x-uniq (gensym))] (dict-set env x-uniq e) x-uniq)))

;; remove-complex-opera* : Lvar -> Lvar^mon
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info ((rco-exp '()) e))]))

(define (explicate_tail e)
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Let x rhs body) (explicate_assign rhs x (explicate_tail body))]
    [(Prim op es) (Return (Prim op es))]
    [else (error "explicate_tail unhandled case" e)]))

(define (explicate_assign e x cont)
  (match e
    [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Let y rhs body) (explicate_assign rhs y (explicate_assign body x cont))]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
    [else (error "explicate_assign unhandled case" e)]))

;; explicate-control : Lvar^mon -> Cvar
(define (explicate-control p)
  (match p
    [(Program info body) (CProgram info `((start . ,(explicate_tail body))))]))

; atm ::= (Int int) | (Var var)
; exp ::= atm | (Prim 'read ()) | (Prim '- (atm)) | (Prim '+ (atm atm)) | (Prim '- (atm atm))
; stmt ::= (Assign (Var var) exp)
; tail ::= (Return exp) | (Seq stmt tail)
; CVar ::=  (CProgram info ((label . tail) ... ))

; reg ::= rsp|rbp|rax|rbx|rcx|rdx|rsi|rdi| r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
; arg ::= (Imm int) | (Reg reg) | (Deref reg int)
; instr ::= (Instr addq (arg arg)) | (Instr subq (arg arg))
;           | (Instr negq (arg)) | (Instr movq (arg arg))
;           | (Instr pushq (arg)) | (Instr popq (arg))
;           | (Callq label int) | (Retq) | (Jmp label)
; block ::= (Block info (instr...))
; x86int ::= (X86Program info ((label . block) ... ))

(define (select_atm a)
  (match a
    [(Int n) (Imm n)]
    [(Var x) (Var x)]
    [(Reg reg) (Reg reg)]))

(define (select_stmt e)
  (match e
    [(Assign x (Int n)) (list (Instr 'movq (list (Imm n) x)))]
    [(Assign x (Var y)) (list (Instr 'movq (list (Var y) x)))]
    [(Assign x (Prim '- (list atm))) (list (Instr 'movq (list (select_atm atm) x)) (Instr 'negq (list x)))]
    [(Assign x (Prim '+ (list atm1 atm2))) (list (Instr 'movq (list (select_atm atm1) x)) (Instr 'addq (list (select_atm atm2) x)))]
    [(Assign x (Prim '- (list atm1 atm2))) (list (Instr 'movq (list (select_atm atm1) x)) (Instr 'subq (list (select_atm atm2) x)))]
    [(Assign x (Prim 'read arg)) (list (Callq 'read_int 0) (Instr 'movq (list (Reg 'rax) x)))]
    ))

(define (select_tail e)
  (match e
    [(Seq stmt tail) (append (select_stmt stmt) (select_tail tail))]
    [(Return ex) (append (select_stmt (Assign (Reg 'rax) ex)) (list (Jmp 'conclusion)))]))

;; stack space
(define (assign-stack-space info)
  (cons (cons 'stack-space (* 16  (+ 1 (quotient (length (cdr (assoc 'locals-types info))) 2)))) info))

;; select-instructions : Cvar -> x86var
(define (select-instructions p)
  (match p
    [(CProgram info body) (X86Program (assign-stack-space info) `((start . ,(Block info (select_tail (cdr (car body)))))))]))

;; assign variables in list from info to a hash map with stack locations
(define (assign-stack list-vars)
  (let ([var-hashmap (make-hash)])
    (map (lambda (var id)
           (hash-set! var-hashmap (car var) (Deref 'rbp (- (* 8 (+ 1 id)))))
           ) list-vars (range (length list-vars)))
    var-hashmap
    )
)

;; take variables inside body and then replace them with their
;; corresponding entries in the hashmap
(define (replace-var body var-hashmap)
  (map (lambda (inst)
         (match inst
           [(Instr instr (list (Var x))) (Instr instr (list (hash-ref var-hashmap x)))]
           [(Instr instr (list (Var x) (Var y))) (Instr instr (list (hash-ref var-hashmap x) (hash-ref var-hashmap y)))]
           [(Instr instr (list (Var x) atm)) (Instr instr (list (hash-ref var-hashmap x) atm))]
           [(Instr instr (list atm (Var x))) (Instr instr (list atm (hash-ref var-hashmap x)))]
           [else inst])) body))

;; assign-homes : x86var -> x86var
(define (assign-homes p)
  (match p
    [(X86Program info (list (cons 'start (Block bl-info body))))
     #:when (list? (assoc 'locals-types info))
     (X86Program (assign-stack-space info) (list (cons 'start (Block bl-info (replace-var body (assign-stack (cdr (assoc 'locals-types info))))))))]
    [else p]))

(define (patch_instr body)
  (foldr (lambda (inst lst)
           (match inst
             [(Instr instr (list (Deref 'rbp n1) (Deref 'rbp n2))) 
              (append (list (Instr 'movq (list (Deref 'rbp n1) (Reg 'rax))) (Instr instr (list (Reg 'rax) (Deref 'rbp n2)))) lst)]
             [(Instr instr (list (Imm n)))
              #:when (> n 2e16)
              (append (list (Instr 'movq (list (Imm n) (Reg 'rax))) (Instr instr (list (Reg 'rax)))) lst)]
             [(Instr instr (list (Imm n) atm))
              #:when (> n 2e16)
              (append (list (Instr 'movq (list (Imm n) (Reg 'rax))) (Instr instr (list (Reg 'rax) atm))) lst)]
             [(Instr instr (list atm (Imm n)))
              #:when (> n 2e16)
              (append (list (Instr 'movq (list (Imm n) (Reg 'rax))) (Instr instr (list atm (Reg 'rax)))) lst)]
             [else (cons inst lst)])) '() body))

;; patch-instructions : x86var -> x86int
(define (patch-instructions p)
   (match p
     [(X86Program info (list (cons 'start (Block bl-info body)))) (X86Program info (list (cons 'start (Block bl-info (patch_instr body)))))]))

;; check system and spit out the correct label, discontinued.
(define (correct-label str)
  (string->uninterned-symbol (if (eq? (system-type 'os) 'macosx)
                                 (string-append "_" str)
                                 str)))
;; add prelude to the body
(define (preludify stack-space body)
  (append body (list `(main . ,(Block '() (list (Instr 'pushq (list (Reg 'rbp)))
                                                              (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
                                                              (Instr 'subq (list (Imm stack-space) (Reg 'rsp)))
                                                              (Jmp 'start)))))))
;; add conclusion to the body
(define (concludify stack-space body)
  (append body (list `(conclusion . ,(Block '() (list (Instr 'addq (list (Imm stack-space) (Reg 'rsp)))
                                                                    (Instr 'popq (list (Reg 'rbp)))
                                                                    (Retq)))))))


;; prelude-and-conclusion : x86int -> x86int
(define (prelude-and-conclusion p)
  (match p
    [(X86Program info body) (let [(stack-space (cdr (assoc 'stack-space info)))]
                              (X86Program info
                                          (concludify stack-space
                                                     (preludify stack-space body))))]))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
; (define compiler-passes
;   `(
;      ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
;      ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
;      ("explicate control" ,explicate-control, interp-Cvar ,type-check-Cvar)
;      ("instruction selection" ,select-instructions ,interp-x86-0)
;      ("assign homes" ,assign-homes ,interp-x86-0)
;      ("patch instructions" ,patch-instructions ,interp-x86-0)
;      ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)))

; (explicate-control (Program '() (Prim '+ (list  (Int 1) (Int 2)))))
; (select-instructions (explicate-control (Program '() (Prim '+ (list  (Int 1) (Int 2))))))
; (explicate-control (remove-complex-opera* (uniquify (Program '() (Let 'y (Let 'x (Int 20) (Prim '+ (list (Var 'x) (Let 'x (Int 22) (Var 'x))))) (Var 'y))))))
; (select-instructions (explicate-control (remove-complex-opera* (uniquify (Program '() (Let 'y (Let 'x (Int 20) (Prim '+ (list (Var 'x) (Let 'x (Int 22) (Var 'x))))) (Var 'y)))))))
; (assign-homes (select-instructions (explicate-control (remove-complex-opera* (uniquify (Program '() (Let 'y (Let 'x (Int 20) (Prim '+ (list (Var 'x) (Let 'x (Int 22) (Var 'x))))) (Var 'y))))))))
; (uniquify (Program '() (Prim '+ (list  (Int 1) (Int 2)))))
; (uniquify (Program '() (Let 'x (Int 43) (Prim '+ (list (Int 43) (Var 'x))))))
; (interp-Lvar (uniquify (Program '() (Let 'x (Int 43) (Prim '+ (list (Let 'x (Int 50) (Prim '+ (list (Var 'x) (Int 10)))) (Var 'x)))))))


;; output for prelude and conclusion 

(define out
  (X86Program
  '((stack-space . 32)
    (stack-space . 32)
    (locals-types (g14349 . Integer) (g14350 . Integer)))
  (list
    (cons
    'start
    (Block
      '((locals-types (g14349 . Integer) (g14350 . Integer))
        (live-after (list (Reg 'rax)) (list (Deref 'rbp -16)) (list (Reg 'rax)) '() (list (Deref 'rbp -8)) (list (Deref 'rbp -8)) (list (Reg 'rax)) '()))
      (list
      (Callq 'read_int 0)
      (Instr 'movq (list (Reg 'rax) (Deref 'rbp -16)))
      (Instr 'movq (list (Deref 'rbp -16) (Reg 'rax)))
      (Instr 'movq (list (Reg 'rax) (Deref 'rbp -8)))
      (Instr 'addq (list (Imm 1) (Deref 'rbp -8)))
      (Instr 'movq (list (Imm 1) (Reg 'rax)))
      (Instr 'addq (list (Deref 'rbp -8) (Reg 'rax)))
      (Jmp 'conclusion))))
    (cons
    'main
    (Block
      '((live-after (list (Reg 'rsp)) (list (Reg 'rbp)) (list (Reg 'rsp) (Reg 'rbp)) '()))
      (list
      (Instr 'pushq (list (Reg 'rbp)))
      (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
      (Instr 'subq (list (Imm 32) (Reg 'rsp)))
      (Jmp 'start))))
    (cons
    'conclusion
    (Block
      '((live-after '() '() '()))
      (list
      (Instr 'addq (list (Imm 32) (Reg 'rsp)))
      (Instr 'popq (list (Reg 'rbp)))
      (Retq)))))))

; register allocation

;; Interference Graph
;; for each instruction - edge between write location(s) and live locations, no interference with itself
;; callq - edge between every live variable and every caller-saved register
;; for movq s,d - if for every v in Lafter(k) if v!=d and v!=s, add edge(v,d)
;; for other instructions - for every d in W(k) and v in Lafter(k), if v!=d, add edge(v,d)
;; work from top to bottom

(define (interference-graph live-after body)
  (foldr (lambda (live instr edges)
          (append (match instr
            [(Instr 'movq (list s d)) (foldr (lambda (v lst)
                                        (cond
                                          [(or (equal? s v) (equal? d v)) (cons (list v d) lst)]
                                          [else lst])) 
                                      '() live)]
            [(cons Callq _) (foldr (lambda (v lst)
                                        (append '((v (Reg 'rax)) (v (Reg 'rcx)) (v (Reg 'rdx)) (v (Reg 'rsi)) 
                                                  (v (Reg 'rdi)) (v (Reg 'r8)) (v (Reg 'r9)) (v (Reg 'r10)) (v (Reg 'r11))) 
                                          lst)) 
                                      '() live)]
            [(Instr 'pushq _) '()]
            [(Instr _ (list s d)) (foldr (lambda (v lst)
                                    (cond
                                      [(equal? d v) (cons (list v d) lst)]
                                      [else lst]))
                                  '() live)]
            [(Instr _ (list d)) (foldr (lambda (v lst)
                                    (cond
                                      [(equal? d v) (cons (list v d) lst)]
                                      [else lst])) 
                                '() live)]
            [else '()]) edges))
        '() live-after body))

; (define (build-blocks body)
;   (map (lambda (block)
;     (match block
;       [(x Block info e) (x Block (list 'interference (interference-graph (cdr (assoc 'live-after info)) e)) e)]))
;     body))

(define (build-blocks body)
  (map (lambda (block)
         (match block
           [(cons x (Block info e)) (cons x (Block (list 'interference (interference-graph (cdr (assoc 'live-after info)) e)) e))]))
        body))

(define (build-interference p)
  (match p
    [(X86Program info body) (X86Program info (build-blocks body))]))

(build-interference out)

; (define (g) (undirected-graph '()))

; (g)
