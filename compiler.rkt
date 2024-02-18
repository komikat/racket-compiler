#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
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

; (define (select_exp e)
;   (match e
;     [(Int n) (Imm n)]
;     [(Var x) (Var x)]
;     [(Prim 'read ()) ]))

(define (select_atm a)
  (match a
    [(Int n) (Imm n)]
    [(Var x) (Var x)]))

(define (select_stmt e)
  (match e
    [(Assign (Var x) (Int n)) ('movq (Imm n) (Var x))]
    [(Assign (Var x) (Var y)) ('movq (Var y) (Var x))]
    ; [(Assign (Var x) (Prim 'read ())) (Seq (callq read_int) (movq %rax (Var x)))]
    [(Assign (Var x) (Prim '- (list atm))) ('negq atm)]
    [(Assign (Var x) (Prim '+ (list atm1 atm2))) (list ('movq (select_atm atm1) (Var x)) ('addq (select_atm atm2) (Var x)))]
    [(Assign (Var x) (Prim '- (list atm1 atm2))) (list ('movq (select_atm atm1) (Var x)) ('subq (select_atm atm2) (Var x)))]
    [(Seq stmt tail) (Seq (select_stmt e) (select_stmt tail))]
    [(Return ex) (select_stmt (Assign ((Var '%rax) ex)))]))

;; select-instructions : Cvar -> x86var
(define (select-instructions p)
  (match p
  [(CProgram info body) 
    (match body
      [(label e) (x86Program info (select_stmt e))])]))

;; assign-homes : x86var -> x86var
(define (assign-homes p)
  (error "TODO: code goes here (assign-homes)"))

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
     ;; ("instruction selection" ,select-instructions ,interp-x86-0)
     ;; ("assign homes" ,assign-homes ,interp-x86-0)
     ;; ("patch instructions" ,patch-instructions ,interp-x86-0)
     ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))

(explicate-control (Program '() (Prim '+ (list  (Int 1) (Int 2)))))
(explicate-control (remove-complex-opera* (uniquify (Program '() (Let 'y (Let 'x (Int 20) (Prim '+ (list (Var 'x) (Let 'x (Int 22) (Var 'x))))) (Var 'y))))))
; (uniquify (Program '() (Prim '+ (list  (Int 1) (Int 2)))))
; (uniquify (Program '() (Let 'x (Int 43) (Prim '+ (list (Int 43) (Var 'x))))))
; (interp-Lvar (uniquify (Program '() (Let 'x (Int 43) (Prim '+ (list (Let 'x (Int 50) (Prim '+ (list (Var 'x) (Int 10)))) (Var 'x)))))))


