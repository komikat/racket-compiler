#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
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
    [(Assign x (Prim 'read '())) (list (Instr 'callq 'read_int) (Instr 'movq (list (Reg 'rax) x)))]
    [(Assign x (Prim '- (list atm))) (list (Instr 'movq (list (select_atm atm) x)) (Instr 'negq (list x)))]
    [(Assign x (Prim '+ (list atm1 atm2))) (list (Instr 'movq (list (select_atm atm1) x)) (Instr 'addq (list (select_atm atm2) x)))]
    [(Assign x (Prim '- (list atm1 atm2))) (list (Instr 'movq (list (select_atm atm1) x)) (Instr 'subq (list (select_atm atm2) x)))]))

(define (select_tail e)
  (match e
    [(Seq stmt tail) (append (select_stmt stmt) (select_tail tail))]
    [(Return ex) (append (select_stmt (Assign (Reg 'rax) ex)) (list (Jmp 'conclusion)))]))

;; select-instructions : Cvar -> x86var
(define (select-instructions p)
  (match p
    [(CProgram info body) (X86Program info `((start . ,(Block info (select_tail (cdr (car body)))))))]))



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
    [(X86Program info (list (cons 'start (Block bl-info body)))) #:when (list? (assoc 'locals-types info))
     (X86Program info (list (cons 'start (Block bl-info (replace-var body (assign-stack (cdr (assoc 'locals-types info))))))))]
    [else p]))


;; patch-instructions : x86var -> x86int
(define (patch-instructions p)
  (error "TODO: code goes here (patch-instructions)"))

;; prelude-and-conclusion : x86int -> x86int
(define (prelude-and-conclusion p)
  (error "TODO: code goes here (prelude-and-conclusion)"))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
     ;; Uncomment the following passes as you finish them.
     ("uniquify", uniquify, interp-Lvar, type-check-Lvar)
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
     ("explicate control", explicate-control, interp-Cvar, type-check-Cvar)
     ("instruction selection" ,select-instructions ,interp-x86-0)
     ("assign homes" ,assign-homes ,interp-x86-0)
     ;; ("patch instructions" ,patch-instructions ,interp-x86-0)
     ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))

; (explicate-control (Program '() (Prim '+ (list  (Int 1) (Int 2)))))
; (select-instructions (explicate-control (Program '() (Prim '+ (list  (Int 1) (Int 2))))))
; (explicate-control (remove-complex-opera* (uniquify (Program '() (Let 'y (Let 'x (Int 20) (Prim '+ (list (Var 'x) (Let 'x (Int 22) (Var 'x))))) (Var 'y))))))
;(assign-homes (select-instructions (explicate-control (remove-complex-opera* (uniquify (Program '() (Let 'y (Let 'x (Int 20) (Prim '+ (list (Var 'x) (Let 'x (Int 22) (Var 'x))))) (Var 'y))))))))
; (uniquify (Program '() (Prim '+ (list  (Int 1) (Int 2)))))
; (uniquify (Program '() (Let 'x (Int 43) (Prim '+ (list (Int 43) (Var 'x))))))
; (interp-Lvar (uniquify (Program '() (Let 'x (Int 43) (Prim '+ (list (Let 'x (Int 50) (Prim '+ (list (Var 'x) (Int 10)))) (Var 'x)))))))


