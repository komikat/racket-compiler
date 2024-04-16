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
(require "utilities.rkt")
(require "interp.rkt")
(require "graph-printing.rkt")
(require "priority_queue.rkt")
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



(define (patch_instr body)
  (foldr (lambda (inst lst)
           (match inst
             [(Instr instr (list (Deref 'rbp n1) (Deref 'rbp n2))) #:when (eq? n1 n2) (remove instr lst)]
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

;; (X86Program
;;  '((stack-space . 16) (stack-space . 16) (locals-types))
;;  (list
;;   (cons
;;    'start
;;    (Block
;;     '((locals-types))
;;     (list (Instr 'movq (list (Imm 42) (Reg 'rax))) (Jmp 'conclusion))))))

;; (X86Program
;;  '((stack-space . 16) (locals-types (g14345 . Integer)))
;;  (list
;;   (cons
;;    'start
;;    (Block
;;     '((locals-types (g14345 . Integer)))
;;     (list
;;      (Instr 'movq (list (Imm 41) (Var 'g14345)))
;;      (Instr 'movq (list (Var 'g14345) (Reg 'rax)))
;;      (Instr 'addq (list (Imm 1) (Reg 'rax)))
;;      (Jmp 'conclusion))))))




;; reg ::= rsp | rbp | rax | rbx | rcx | rdx | rsi | rdi |
;;         r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
;; arg ::= (Imm int) | (Reg reg) | (Deref reg int)
;; instr ::= (Instr addq (arg arg)) | (Instr subq (arg arg)) |
;;           (Instr negq (arg)) | (Instr movq (arg arg)) |
;;           (Instr pushq (arg)) | (Instr popq (arg)) |
;;           (Callq label int) | (Retq) | (Jmp label)
;; block ::= (Block info (instr … ))
;; x86Int ::= (X86Program info ((label . block) … ))

;; compute the set of locations read by an instruction
;; arg? -> (set)
(define (get-loc arg)
  (match arg
    [(Reg r) (set r)]
    [(Var x) (set x)]
    [(Imm m) (set)]
    [(Deref r i) (set r)]
    ))

(define arg-passing-regs '(rdi rsi rdx rcx r8 r9))

;; locations written by an instruction
;; Instr? -> set?
(define (write-locs instr)
  (match instr
    [(Instr q (list _ a)) #:when (member q (list 'addq 'subq)) (get-loc a)]
    [(Instr q (list a)) #:when (member q (list 'negq)) (get-loc a)] ;; ASSUMPTION: pushq popq are not reading the locations
    [(Instr 'movq (list _ a2)) (get-loc a2)]
    [(Retq) (set)]
    ([Callq _ _] caller-save) 
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

;; Interference Graph
;; for each instruction - edge between write location(s) and live locations, no interference with itself
;; callq - edge between every live variable and every caller-saved register
;; for movq s,d - if for every v in Lafter(k) if v!=d and v!=s, add edge(v,d)
;; for other instructions - for every d in W(k) and v in Lafter(k), if v!=d, add edge(v,d)
;; work from top to bottom

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

(define color-regs (hash 0 'rcx 1 'rdx 2 'rsi 3 'rdi 4 'r8 5 'r9 6 'r10 7 'rbx 8 'r12 9 'r13))

;; greedy
;; graph?, hash? -> [set?]
(define (update-num-spills spills c)
  (cond [(>= c (num-registers-for-alloc))
         (add1 spills)]
        [else spills]
        ))

(define (color-graph graph info)
  (define locals (map car (dict-ref info 'locals-types)))
  (define num-spills 0)
  (define uncolors (make-hash))
  (define (compare u v)
    (>= (set-count (hash-ref uncolors u))
        (set-count (hash-ref uncolors v))))
  (define Q (make-pqueue compare))
  (define pq->node (make-hash))
  (define var->color (make-hash))

  (for ([x locals])
    (define adj-reg
      (filter (lambda (u) (set-member? registers u))
              (get-neighbors graph x)))
    (define adj-colors (list->set (map register->color adj-reg)))
    (hash-set! uncolors x adj-colors)
    (hash-set! pq->node x (pqueue-push! Q x)))

  
  (while (> (pqueue-count Q) 0)
    (define v (pqueue-pop! Q))
    (define c (for/first ([c (in-naturals)]
                          #:when (not (set-member? (hash-ref uncolors v) c)))
                c))
    (verbose (format "color of ~a is ~a" v c))
    (set! num-spills (update-num-spills num-spills c))
    (hash-set! var->color v c)
    (for ([u (in-neighbors graph v)])
      (when (not (set-member? registers u))
        (hash-set! uncolors u
                   (set-add (hash-ref uncolors u) c))
        (pqueue-decrease-key! Q (hash-ref pq->node u)))))
  (cons var->color num-spills))

;; take every variable
;; get color from color-graph
;; get color register (if in bounds)
;; else pass to assign stack
(define (assign-register list-vars color-graph)
  (define var-to-register-hash (make-hash))
  (define spill-list '())
  (for-each (lambda (var)
              (let ((color (hash-ref color-graph var)))
                (if (>= color (hash-count color-regs))
                    (set! spill-list (cons var spill-list))                    
                    (let ((register (hash-ref color-regs color)))
                      (hash-set! var-to-register-hash var (Reg register))))))
            list-vars)
  (println "===varreg===")

  (println var-to-register-hash)

  (define callee-length (set-count (get-used-callee var-to-register-hash)))
  (assign-stack spill-list var-to-register-hash callee-length))

;; assign variables in list from info to a hash map with stack locations
(define (assign-stack list-vars var-register-hashmap callee-length)
  (let ([var-hashmap var-register-hashmap])
    (map (lambda (var id)
           (hash-set! var-hashmap var (Deref 'rbp (- (* 8 (+ callee-length 1 id)))))
           ) list-vars (range (length list-vars)))
    var-hashmap))


(define (get-used-callee var-hashmap)
  (set-remove (list->set (hash-map var-hashmap (lambda (variable location)
                                                 (match location
                                                   [(Reg x) #:when (not (eq? #f (set-member? callee-save x))) x]
                                                   [else '()]
                                                   )))) '()))

(define (get-stack-locations var-hashmap)
  (set-remove (list->set (hash-map var-hashmap (lambda (variable location)
                                                 (match location
                                                   [(Deref 'rbp x) x]
                                                   [else '()]
                                                   )))) '()))

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

(define (allocate-registers p)
  (match p
    [(X86Program info (list (cons 'start (Block bl-info body))))
     #:when (list? (assoc 'locals-types info))
     
     (let ([list-vars (map car (cdr (assoc 'locals-types bl-info)))])
       (define colored-graph-result (color-graph (cdr (assoc 'conflicts bl-info)) info))
       (define num-spills (cdr colored-graph-result))
       (define colored-graph (car colored-graph-result))
       (let ((var-hashmap (assign-register list-vars colored-graph)))
         (X86Program (dict-set
                      (dict-set info 'used-callee (get-used-callee var-hashmap))
                      'stack-locs num-spills)
                     (list (cons 'start (Block bl-info (replace-var body var-hashmap)))))))]
    [else p]))


(define (get-S p)
  (match p
    [(X86Program info body) (cdr (assoc 'stack-locs info))]))

(define (program->used-callee p)
  (match p
    [(X86Program info body) (cdr (assoc 'used-callee info))]))



;; add prelude to the body
(define (preludify used-callee stack-space body)
  (append body (list `(main . ,(Block '() (append (list (Instr 'pushq (list (Reg 'rbp)))
                                                        (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
                                                        (Instr 'subq (list (Imm stack-space) (Reg 'rsp))))
                                                (set-map used-callee (lambda (r) (Instr 'pushq (list (Reg r)))))
                                                (list (Jmp 'start))))))))
;; add conclusion to the body
(define (concludify used-callee stack-space body)
  (append body (list `(conclusion . ,(Block '() (append (list (Instr 'addq (list (Imm stack-space) (Reg 'rsp))))
                                                        (set-map used-callee (lambda (r) (Instr 'popq (list (Reg r)))))
                                                        (list  (Instr 'popq (list (Reg 'rbp)))
                                                               (Retq))))))))


;; prelude-and-conclusion : x86int -> x86int
(define (prelude-and-conclusion p)
  (define used-callee (program->used-callee p))
  (define C (set-count used-callee))
  (define S (get-S p))
  (define A (- (align (* 8 (+ S C)) 16) (* 8 C)))
  (match p
    [(X86Program info body) (X86Program info
                                        (concludify used-callee A
                                                    (preludify used-callee A body)))]))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
    ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
    ("explicate control" ,explicate-control, interp-Cvar ,type-check-Cvar)
    ("instruction selection" ,select-instructions ,interp-x86-0)
    ;("assign homes" ,assign-homes ,interp-x86-0)
    ("uncover live" ,uncover-live ,interp-x86-0)
    ("build interference" ,build-interference ,interp-x86-0)
    ("allocate registers" ,allocate-registers ,interp-x86-0)
    ("patch instructions" ,patch-instructions ,interp-x86-0)
    ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)))
