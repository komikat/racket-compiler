#lang racket

(require racket/match)
(require racket/list)
(require racket/set)
(require racket/set racket/stream)
(require racket/fixnum)
(require racket/match)
(require graph)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "interp-Lif.rkt")
(require "interp-Cif.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Cif.rkt")
(require "utilities.rkt")
(require "interp.rkt")
(provide (all-defined-out))

(define (remove-and-or e)
  (match e
    [(or (Bool _) (Int _) (Var _)) e]
    [(If e1 e2 e3) (If (remove-and-or e1) (remove-and-or e2) (remove-and-or e3))]
    [(Prim 'and (list e1 e2)) (If (remove-and-or e1) (remove-and-or e2) (Bool #f))]
    [(Prim 'or (list e1 e2)) (If (remove-and-or e1) (Bool #t) (remove-and-or e2))]
    [(Prim op (list e1 e2)) (Prim op (list (remove-and-or e1) (remove-and-or e2)))]
    [(Prim op (list e1)) (Prim op (list (remove-and-or e1)))]
    [(Let x e body) (Let x (remove-and-or e) (remove-and-or body))]))

(define (shrink p)
  (match p
    [(Program info body) (Program info (remove-and-or body))]))

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x) (Var (dict-ref env x))]
      [(or (Int _) (Bool _)) e]
      [(Let x e body) (let [(x-uniq (gensym))]
                        (let [(new-uniq-pass (uniquify-exp (dict-set env x x-uniq)))]
                          (Let x-uniq (new-uniq-pass e) (new-uniq-pass body))))]
      [(If e1 e2 e3) (If ((uniquify-exp env) e1) ((uniquify-exp env) e2) ((uniquify-exp env) e3))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : Lvar -> Lvar
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

; (uniquify (Program '() (Let 'x (Int 15) (Let 'y (Prim '+ (list (Int 5) (Int 4))) (Prim '+ (list (Int 10) (Prim '- (list (Var 'x) (Var 'y)))))))))
; (uniquify (Program '() (If (Prim 'and (list (Bool #t) (Bool #f))) (Bool #t) (Bool #f))))

(define (rco-exp env)
  (lambda (e)
    (match e
      [(Let x e body) (Let x ((rco-exp env) e) ((rco-exp env) body))]
      [(or (Int _) (Var _) (Bool _)) e]
      [(Prim 'read '()) (Prim 'read '())]
      [(Prim op (list (or (Int _) (Var _) (Bool _)))) e]
      [(Prim op (list (or (Int _) (Var _) (Bool _)) (or (Var _) (Int _) (Bool _)))) e]
      [(Prim op (list e2)) (let [(x ((rco-atom env) e2))] (Let x ((rco-exp env) e2) (Prim op (list (Var x)))))]
      [(Prim op (list e1 e2)) #:when (or (Int? e1) (Var? e1) (Bool? e1)) (let [(x ((rco-atom env) e2))] (Let x ((rco-exp env) e2) (Prim op (list e1 (Var x)))))]
      [(Prim op (list e1 e2)) #:when (or (Int? e2) (Var? e2)) (let [(x ((rco-atom env) e1))] (Let x ((rco-exp env) e1) (Prim op (list (Var x) e2))))]
      [(Prim op (list e1 e2)) (let [(x ((rco-atom env) e1))] (let [(y ((rco-atom env) e2))] (Let x ((rco-exp env) e1) (Let y ((rco-exp env) e2) (Prim op (list (Var x) (Var y)))))))]
      [(If e1 e2 e3) (If ((rco-exp env) e1) ((rco-exp env) e2) ((rco-exp env) e3))])))
      
(define (rco-atom env)
  (lambda (e)
    (let [(x-uniq (gensym))] (dict-set env x-uniq e) x-uniq)))

;; remove-complex-opera* : Lvar -> Lvar^mon
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info ((rco-exp '()) e))]))

(define (explicate_tail e)
  (match e
    [(Bool b) (Return (Bool b))]
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Let x rhs body) (explicate_assign rhs x (explicate_tail body))]
    [(Prim op es) (Return (Prim op es))]
    [(If cnd thn els) (explicate_pred cnd (explicate_tail thn) (explicate_tail els))]
    [else (error "explicate_tail unhandled case" e)]))

(define (explicate_assign e x cont)
  (match e
    [(Bool b) (Seq (Assign (Var x) (Bool b)) cont)]
    [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Let y rhs body) (explicate_assign rhs y (explicate_assign body x cont))]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
    [(If cnd thn els) (Seq (Assign (Var x) œ(explicate_pred cnd (explicate_tail thn) (explicate_tail els))))]
    [else (error "explicate_assign unhandled case" e)]))

(define basic-blocks '())

(define (create_block tail) 
  (match tail
    [(Goto label) (Goto label)] 
    [else 
      (let ([label (gensym 'block)])
        (set! basic-blocks (cons (cons label tail) basic-blocks)) 
        (Goto label))]))

(define (explicate_let_in_if e thn els)
  (match e
    [(or (Bool _) (Int _) (Var _)) (explicate_pred e thn els)]
    [(Prim op es) (explicate_pred (Prim op es) thn els)]
    [(If _ _ _) (explicate_pred e thn els)]
    [(Let x rhs body) (explicate_assign rhs x (explicate_let_in_if body thn els))]))

(define (explicate_pred cnd thn els) 
  (match cnd
    [(Var x) (IfStmt (Prim 'eq? (list (Var x) (Int 0))) 
                (create_block els) (create_block thn))]
    [(Int n) (IfStmt (Prim 'eq? (list (Int n) (Int 0))) 
                (create_block els) (create_block thn))]
    [(Let x rhs body) (explicate_assign rhs x (explicate_let_in_if body thn els))]
    [(Prim 'not (list e)) (explicate_pred e els thn)]
    [(Prim op es)
      (IfStmt (Prim op es) (create_block thn) (create_block els))]
    [(Bool b) (if b thn els)]
    [(If cnd^ thn^ els^) (explicate_pred cnd^ 
                          (create_block (explicate_pred thn^ thn els)) 
                          (create_block (explicate_pred els^ thn els)))]
    [else (error "explicate_pred unhandled case" cnd)]))

(define (explicate-wrap body info)
  (set! basic-blocks (cons (cons 'start (explicate_tail body)) basic-blocks)) 
  basic-blocks)

;; explicate-control : Lvar^mon -> Cvar
(define (explicate-control p)
  (match p
    [(Program info body) (CProgram info (explicate-wrap body info))]))

(explicate-control (remove-complex-opera* (uniquify (shrink (Program
 '()
 (If
  (If
   (Prim '> (list (Int 4) (Int 8)))
   (Prim 'eq? (list (Int 1) (Int 1)))
   (Bool #f))
  (Let
   'g22647
   (Int 4)
   (Prim
    '+
    (list
     (Prim '+ (list (Var 'g22647) (Int 8)))
     (If
      (If
       (Prim 'eq? (list (Int 1) (Int 1)))
       (Prim '<= (list (Var 'g22647) (Int 4)))
       (Bool #t))
      (Int 14)
      (Int 0)))))
  (Int 5)))))))


(define (select_atm a)
  (match a
    [(Bool #t) (Imm 1)]
    [(Bool #f) (Imm 0)]
    [(Int n) (Imm n)]
    [(Var x) (Var x)]
    [(Reg reg) (Reg reg)]))

; atm ::= (Bool bool)
; cmp ::= eq?|<|<=|>|>=
; exp ::= (Prim ’not (atm)) | (Prim ’cmp (atm atm))
; tail ::= (Goto label) | (IfStmt (Prim cmp (atm atm)) (Goto label) (Goto label))
; Cif ::= (CProgram info ((label . tail) ... ))

(define (select_stmt e)
  (match e
    [(Assign x (Bool #t)) (list (Instr 'movq (list (Imm 1) x)))]
    [(Assign x (Bool #f)) (list (Instr 'movq (list (Imm 0) x)))]
    [(Assign x (Int n)) (list (Instr 'movq (list (Imm n) x)))]
    [(Assign x (Var y)) (list (Instr 'movq (list (Var y) x)))]
    [(Assign x (Prim '- (list atm))) (list (Instr 'movq (list (select_atm atm) x)) (Instr 'negq (list x)))]
    [(Assign x (Prim 'not (list x))) (list (Instr 'xorq (list (Imm 1) x)))]
    [(Assign x (Prim 'not (list atm))) (list (Instr 'movq (list (select_atm atm) x)) (Instr 'xorq (list (Imm 1) x)))]
    [(Assign x (Prim '+ (list atm1 atm2))) (list (Instr 'movq (list (select_atm atm1) x)) (Instr 'addq (list (select_atm atm2) x)))]
    [(Assign x (Prim '- (list atm1 atm2))) (list (Instr 'movq (list (select_atm atm1) x)) (Instr 'subq (list (select_atm atm2) x)))]
    [(Assign x (Prim 'read arg)) (list (Callq 'read_int 0) (Instr 'movq (list (Reg 'rax) x)))]
    [(Assign x (Prim 'eq? (list atm1 atm2))) (list (Instr 'cmpq (list (select_atm atm1) (select_atm atm2)))
                                                (Instr 'sete (list (Reg 'al)))
                                                (Instr 'movzbq (list (Reg 'al) x)))]
    [(Assign x (Prim '< (list atm1 atm2))) (list (Instr 'cmpq (list (select_atm atm1) (select_atm atm2)))
                                                (Instr 'setl (list (Reg 'al)))
                                                (Instr 'movzbq (list (Reg 'al) x)))]
    [(Assign x (Prim '<= (list atm1 atm2))) (list (Instr 'cmpq (list (select_atm atm1) (select_atm atm2)))
                                                (Instr 'setle (list (Reg 'al)))
                                                (Instr 'movzbq (list (Reg 'al) x)))]
    [(Assign x (Prim '> (list atm1 atm2))) (list (Instr 'cmpq (list (select_atm atm1) (select_atm atm2)))
                                                (Instr 'setg (list (Reg 'al)))
                                                (Instr 'movzbq (list (Reg 'al) x)))]
    [(Assign x (Prim '>= (list atm1 atm2))) (list (Instr 'cmpq (list (select_atm atm1) (select_atm atm2)))
                                                (Instr 'setge (list (Reg 'al)))
                                                (Instr 'movzbq (list (Reg 'al) x)))]))


(define (select_tail e)
  (match e
    [(IfStmt (Prim 'eq? (list atm1 atm2)) (Goto l1) (Goto l2)) (list (Instr 'cmpq (list (select_atm atm1) (select_atm atm2)))
                                                                  (Instr 'je l1)
                                                                  (Jmp l2))]
    [(IfStmt (Prim '> (list atm1 atm2)) (Goto l1) (Goto l2)) (list (Instr 'cmpq (list (select_atm atm1) (select_atm atm2)))
                                                                  (Instr 'jg l1)
                                                                  (Jmp l2))]
    [(IfStmt (Prim '>= (list atm1 atm2)) (Goto l1) (Goto l2)) (list (Instr 'cmpq (list (select_atm atm1) (select_atm atm2)))
                                                                  (Instr 'jge l1)
                                                                  (Jmp l2))]    
    [(IfStmt (Prim '< (list atm1 atm2)) (Goto l1) (Goto l2)) (list (Instr 'cmpq (list (select_atm atm1) (select_atm atm2)))
                                                                  (Instr 'jl l1)
                                                                  (Jmp l2))]
    [(IfStmt (Prim '<= (list atm1 atm2)) (Goto l1) (Goto l2)) (list (Instr 'cmpq (list (select_atm atm1) (select_atm atm2)))
                                                                  (Instr 'jle l1)
                                                                  (Jmp l2))]
    [(Goto l) (Jmp l)]                                                                                                                                                                                                                                             
    [(Seq stmt tail) (append (select_stmt stmt) (select_tail tail))]
    [(Return ex) (append (select_stmt (Assign (Reg 'rax) ex)) (list (Jmp 'conclusion)))]))

;; stack space
(define (assign-stack-space info)
  (cons (cons 'stack-space (* 16  (+ 1 (quotient (length (cdr (assoc 'locals-types info))) 2)))) info))

;; select-instructions : Cvar -> x86var
(define (select-instructions p)
  (match p
    [(CProgram info body) (X86Program (assign-stack-space info) `((start . ,(Block info (select_tail (cdr (car body)))))))]))


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

;; check system and spit out the correct label
;; Discontinued.
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


;; compute the set of locations read by an instruction
;; arg? -> (set)
(define (get-loc arg)
  (match arg
    [(Reg r) (set r)]
    [(Var x) (set x)]
    [(Imm m) (set)]
    ))

(define caller-saved-regs (set 'rax 'rcx 'rdx 'rsi 'rdi 'r8 'r9 'r10 'r11))
(define arg-passing-regs '(rdi rsi rdx rcx r8 r9))

;; locations written by an instruction
;; Instr? -> set?
(define (write-locs instr)
  (match instr
    [(Instr q (list _ a)) #:when (member q (list 'addq 'subq)) (get-loc a)]
    [(Instr q (list a)) #:when (member q (list 'negq)) (get-loc a)] ;; ASSUMPTION: pushq popq are not reading the locations
    [(Instr 'movq (list _ a2)) (get-loc a2)]
    [(Retq) (set)]
    ([Callq _ _] caller-saved-regs) 
    ([Jmp _] (set)) ;; TODO
    ))

;; locations read by an instruction
;; Instr? -> set?
(define (read-locs instr)
  (match instr
    [(Instr q (list a1 a2)) #:when (member q (list 'addq 'subq)) (set-union (get-loc a1) (get-loc a2))]
    [(Instr q (list a)) #:when (member q (list 'negq)) (get-loc a)] ;; ASSUMPTION: pushq popq are not reading the locations
    [(Instr 'movq (list a1 a2)) (get-loc a1)]
    [(Retq) (set)]
    ([Callq _ arity] (list->set (drop-right arg-passing-regs (- (length arg-passing-regs) arity)))) 
    ([Jmp 'conclusion] (set 'rax 'rsp))
    ))

;; (Instr?, set?) -> set?
(define (live-after-k-1 instr live-after-k)
  (set-union (set-subtract live-after-k (write-locs instr)) (read-locs instr)))

;; Int? -> list?
(define (sub-instr l)
  (build-list (length l) (lambda (x) (drop l x))))

;; ([Instr?], set?) -> [set?]
(define (instr-to-live-after instrs initial)
  (map (lambda (l-instr)
         (foldr live-after-k-1 initial l-instr)) (sub-instr instrs))
  )

(define (update-blocks Block-pair)
  (match Block-pair
    [(cons label (Block info instrs)) (cons label (Block (dict-set info 'live-after (instr-to-live-after instrs (set))) instrs))]))

;; TODO
(define (label-live Block-pair)
  (match Block-pair
    [(cons label (Block info instrs)) (cons label (instr-to-live-after instrs (set)))]))

(define (uncover-live p)
  (match p
    [(X86Program info Block-alist) (X86Program info (map update-blocks Block-alist))]))

(define (get-final arg)
  (match arg
    [(Reg r) r]
    [(Var x) x]
    [(Imm m) '()] ;; TODO
    ))

; register allocation

(define (find-edges live-after body)
  (foldr (lambda (live instr edges)
           (append (match instr
                     [(Instr 'movq (list s d)) (foldr (lambda (v lst)
                                                        (cond
                                                          [(and (not (equal? (get-final s) v)) (not (equal? (get-final d) v))) (cons (list v (get-final d)) lst)]
                                                          [else lst])) 
                                                      '() (set->list live))]
                     [(Callq _ _) (foldr (lambda (v lst)
                                           (append (list (list v 'rax) (list v 'rcx) (list v 'rdx) (list v 'rsi) 
                                                         (list v 'rdi) (list v 'r8) (list v 'r9) (list v 'r10) (list v 'r11)) 
                                                   lst)) 
                                         '() (set->list live))]
                     [(Instr 'pushq _) '()]
                     [(Instr _ (list s d)) (foldr (lambda (v lst)
                                                    (cond
                                                      [(not (equal? (get-final d) v)) (cons (list v (get-final d)) lst)]
                                                      [else lst]))
                                                  '() (set->list live))]
                     [(Instr _ (list d)) (foldr (lambda (v lst)
                                                  (cond
                                                    [(not (equal? (get-final d) v)) (cons (list v (get-final d)) lst)]
                                                    [else lst])) 
                                                '() (set->list live))]
                     [else '()]) edges))
         '() live-after body))

(define (interference-graph live-after body)
  (undirected-graph (set->list (list->set (find-edges live-after body)))))

(define (build-blocks body)
  (map (lambda (block)
         (match block
           [(cons x (Block info e)) (cons x (Block (dict-set info 'conflicts (interference-graph (cdr (assoc 'live-after info)) e)) e))]))
        body))

(define (build-interference p)
  (match p
    [(X86Program info body) (X86Program info (build-blocks body))]))

(define init-colors (hash 'rcx 0 'rdx 1 'rsi 2 'rdi 3 'r8 4 'r9 5 'r10 6 'rbx 7 'r12 8 'r13 9 'r14 10 'rax -1 'rsp -2 'rbp -3 'r11 -4 'r15 -5))
(define color-regs (hash 0 'rcx 1 'rdx 2 'rsi 3 'rdi 4 'r8 5 'r9 6 'r10 7 'rbx 8 'r12 9 'r13 10 'r14))


;; greedy
;; graph?, hash? -> [set?]
(define (compute-saturation-hash-count graph colors vars)
  (define saturation-hash (make-hash))
  (for-each (lambda (vertex)
              (let ((saturation-set (list->set (map (lambda (neighbor) (hash-ref colors neighbor))
                                                    (filter (lambda (neighbor) (hash-has-key? colors neighbor))
                                                            (get-neighbors graph vertex))))))
                (hash-set! saturation-hash vertex (set-count saturation-set))))
            vars)
  saturation-hash)

(define (key-with-highest-value hash-table)
  (car (let ((key-value-pairs (hash-map hash-table (lambda (key value) (cons key value)))))
         (foldl (lambda (pair current-best)
                  (if (or (not current-best) (> (cdr pair) (cdr current-best)))
                      pair
                      current-best))
                #f
                key-value-pairs))))

(define (remove-values small big)
  (filter (lambda (x) (not (member x small))) big))

;; lowest color not in adjacent
(define (lowest-color colors adjacent)
  (apply min (remove-values
              (map (lambda (register) (hash-ref colors register))
                   (filter (lambda (x) (hash-has-key? colors x)) adjacent))
              (build-list 100 values))))

(define (color-graph graph vars [colors init-colors])
  (if (eq? (length vars) 0) colors
      (let [(highest-satur-var (key-with-highest-value (compute-saturation-hash-count graph colors vars)))]
        (color-graph graph (remove highest-satur-var vars)
                     (hash-set colors highest-satur-var (lowest-color colors (get-neighbors graph highest-satur-var))))))
  )

;; take every variable
;; get color from color-graph
;; get color register (if in bounds)
;; else pass to assign stack

(define (assign-register list-vars color-graph)
  (define var-to-register-hash (make-hash))
  (for-each (lambda (var)
              (let ((color (hash-ref color-graph var)))
                (let ((register (hash-ref color-regs color)))
                  (hash-set! var-to-register-hash var (Reg register)))))
            list-vars)
  var-to-register-hash)

;; assign variables in list from info to a hash map with stack locations
(define (assign-stack list-vars var-register-hashmap)
  (let ([var-hashmap var-register-hashmap])
    (map (lambda (var id)
           (hash-set! var-hashmap (car var) (Deref 'rbp (- (* 8 (+ 1 id)))))
           ) list-vars (range (length list-vars)))
    var-hashmap))

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
(define (allocate-registers p)
  (match p
    [(X86Program info (list (cons 'start (Block bl-info body))))
     #:when (list? (assoc 'locals-types info))
     (let ([list-vars (map car (cdr (assoc 'locals-types bl-info)))])
       (X86Program info (list (cons 'start (Block bl-info (replace-var body (assign-register list-vars
                                                                                             (color-graph (cdr (assoc 'conflicts bl-info))
                                                                                                           list-vars))))))))]
    [else p]))

; (shrink (Program '() (If (Prim 'and (list (Bool #t) (Let 'x (Int 4) (Prim 'or (list (Var 'x) (Prim 'not (list (Bool #f)))))))) (Bool #t) (Bool #f))))
; (shrink (Program '() (If (Prim 'and `(,(Prim '- '((Int 5))) ,(Bool #f))) (Int 42) (Int 42))))


;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
    ; ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
    ; ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
    ; ("explicate control" ,explicate-control, interp-Cvar ,type-check-Cvar)
    ; ("instruction selection" ,select-instructions ,interp-x86-0)
    ; ;("assign homes" ,assign-homes ,interp-x86-0)
    ; ("uncover live" ,uncover-live ,interp-x86-0)
    ; ("build interference" ,build-interference ,interp-x86-0)
    ; ("allocate registers" ,allocate-registers ,interp-x86-0)
    ; ("patch instructions" ,patch-instructions ,interp-x86-0)
    ; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
    ("shrink" ,shrink ,interp-Lif ,type-check-Lif)
    ("uniquify" ,uniquify ,interp-Lif ,type-check-Lif)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lif ,type-check-Lif)
    ("explicate control" ,explicate-control ,interp-Cif ,type-check-Cif)))
    ; ("instruction select" ,select-instructions ,interp-pseudo-x86-1)))

