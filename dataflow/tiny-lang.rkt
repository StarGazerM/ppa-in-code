;; In dataflow analysis chapter, all example is build on a little `WHILE` imperative language(page 4) only
;; include bool and number, since we are focus on intraprocedure analysis, we don't care about
;; function here
;; here is the definition predicate (in s-expression style)

;; Yihao Sun <ysun67@syr.edu>
;; 2020 Syracuse

#lang racket

(provide (all-defined-out))

;; variable is symbol
(define variable? symbol?)

;; arithmetic operator
(define (op-a? o) (member o '(+ - * /)))

;; boolean
(define (op-b? o) (member o '(not and or)))

;; relational operator
(define (op-r? o) (member o '(> < >= <= ==)))

;; arithmetic expression, slightly different
(define (aexpr? ae)
  (match ae
    [(? variable?) #t]
    [(? number?) #t]
    [`(,(? op-a?) ,(? aexpr?) ...) #t]
    [else #f]))

(define (bexpr? be)
  (match be
    [(? boolean?) #t]
    [`(,(? op-b?) ,(? bexpr?) ...) #t]
    [`(,(? op-r?) ,(? aexpr?) ...) #t]
    [else #f]))

;; proc
;; function definition
(define (call? c)
  [`(,lc ,lr call ,p (,as ...)) #t]
  [else #f])
(define (definition? d)
  (match d
    [`(,lx proc ,p (val (,xs ...) res ,y) ,ln is ,s end)
     #t]
    [else #f]))
;; program
(define (program p)
  (match p
    [`(begin (,d* ...) (,s* ...) end) #t]
    [else #f]))


;; get sub expression inside a aexpr
;; note: var and number will not count
(define (aexpr-a a)
  (match a
    [`(,(? op-a?) ,(? aexpr? aes) ...)
     (cons a (foldl (λ (ae res) (set-union res (aexpr-a ae))) '() aes))]
    [else '()]))

;; get sub arithmetic inside a boolean expression
(define (aexpr-b b)
  (match b
    [`(,(? op-r?) ,(? aexpr? aes) ...)
     (filter (λ (a) (not (symbol? a))) aes)]
    [else '()]))

;; change name here
;; all sub arithmetic expression in a statement
(define (aexpr* st)
  (match st
    [(? aexpr?) (aexpr-a st)]
    [(? bexpr?) (aexpr-b st)]
    [`(,label = ,(? variable? x) ,(? aexpr? a)) (aexpr-a a)]
    [`(,label SKIP) '()]
    ;; sequence, for here I just use list
    [`(,(? stmt? sts) ...)
     (foldl (λ (s res) (set-union res (aexpr* s))) '() sts)]
    [`(if (,label ,(? bexpr? b)) ,(? stmt? s1) ,(? stmt? s2))
     (set-union (aexpr-b b)
                (aexpr* s1)
                (aexpr* s2))]
    [`(while (,label ,(? bexpr? b)) do ,(? stmt? s))
     (set-union (aexpr-b b) (aexpr* s))]
    ;; extend with procedure
    [`(begin (,d* ...) (,s* ...) end)
     (define ae-d*
       (foldl (λ (d res) (set-union (aexpr* d) res)) '() d*))
     (define ae-s*
       (foldl (λ (s res) (set-union (aexpr* s) res)) '() s*))
     (set-union ae-d* ae-s*)]
    ;; ln is entry to procedure body, and lx is exit
    [`(,lx proc ,p (val (,x ...) res ,y) ,ln is ,s end)
     (aexpr* s)]
    ;; lc used for call of procedure, lr used for associated return
    [`(,lc ,lr call ,p (,as ...))
     (foldl (λ (a res) (set-union (aexpr* a) res)) '() as)]
    ))

;; check if a variable is a free var inside a Arithmetic Expression
;; isFreeVar : Var → AExpr → Bool
(define (isFreeVar v ae)
  (match ae
    [(? variable?) (equal? v ae)]
    [`(,(? op-a?) ,(? aexpr? aes-prime) ...)
     (ormap (λ (a) (isFreeVar v a)) aes-prime)]
    [else #f]))

(define (free-var? v s)
  (match s
    [(? variable?) (equal? v s)]
    [`(,(? op-a?) ,(? aexpr? aes-prime) ...)
     (ormap (λ (a) (free-var? v a)) aes-prime)]
    [`(,(? op-b?) ,(? bexpr? bs) ...)
     (ormap (λ (b) (free-var? v b)) bs)]
    [`(,(? op-r?) ,(? aexpr? as) ...)
     (ormap (λ (a) (free-var? v a)) as)]
    ;; assignment
    [`(,label = ,(? variable? x) ,(? aexpr? a))
     (or (equal? x v)
         (free-var? v a))]
    ;; sequence, for here I just use list
    [`(,(? stmt? ss) ...)
     (ormap (λ (s) (free-var? v s)) ss)]
    [`(if (,label ,(? bexpr? b)) ,(? stmt? s1) ,(? stmt? s2))
     (or (free-var? v b)
         (free-var? v s1)
         (free-var? v s2))]
    [`(while (,label ,(? bexpr? b)) do ,(? stmt? s))
     (or (free-var? v b)
         (free-var? v s))]
    ;; proc
    [`(begin (,d* ...) (,s* ...) end)
     (or (ormap (λ (d) (free-var? v d)) d*)
         (ormap (λ (s) (free-var? v s)) s*))]
    [`(,lx proc ,p (val (,xs ...) res ,y) ,ln is ,s end)
     (free-var? v s)]
    [`(,lc ,lr call ,p (,as ...))
     (ormap (λ (a) (free-var? v a)) as)]
    [else #f]))

;; get all free var inside a statement
(define (free-vars s)
  (match s
    [(? variable?) (list s)]
    [`(,(? op-a?) ,(? aexpr? aes-prime) ...)
     (foldl (λ (a res) (set-union res (free-vars a))) '() aes-prime)]
    [`(,(? op-b?) ,(? bexpr? bs) ...)
     (foldl (λ (b res) (set-union res (free-vars b))) '() bs)]
    [`(,(? op-r?) ,(? aexpr? as) ...)
     (foldl (λ (a res) (set-union res (free-vars a))) '() as)]
    ;; assignment
    [`(,label = ,(? variable? x) ,(? aexpr? a))
     (set-add (free-vars a) x)]
    ;; sequence, for here I just use list
    [`(,(? stmt? ss) ...)
     (foldl (λ (s res) (set-union res (free-vars s))) '() ss)]
    [`(if (,label ,(? bexpr? b)) ,(? stmt? s1) ,(? stmt? s2))
     (set-union (free-vars b)
                (free-vars s1)
                (free-vars s2))]
    [`(while (,label ,(? bexpr? b)) do ,(? stmt? s))
     (set-union (free-vars b)
                (free-vars s))]
    ;; proc
    [`(begin (,d* ...) (,s* ...) end)
     (define fv-d* (foldl (λ (d res) (set-union res (free-vars d))) '() d*))
     (define fv-s* (foldl (λ (s res) (set-union res (free-vars s))) '() s*))
     (set-union fv-d* fv-s*)]
    [`(,lx proc ,p (val (,xs ...) res ,y) ,ln is ,s end)
     (free-vars s)]
    [`(,lc ,lr call ,p (,as ...))
     (foldl (λ (a res) (set-union res (free-vars a))) '() as)]
    [else '()]))

;; statement
;; in this language all statement is pre-labaled
(define (stmt? st)
  (match st
    ;; assignment
    [`(,label = ,(? variable? x) ,(? aexpr? a)) #t]
    [`(,label SKIP) #t]
    ;; sequence, for here I just use list
    [`(,(? stmt? ss) ...) #t]
    [`(if (,label ,(? bexpr? b)) ,(? stmt? s1) ,(? stmt? s2)) #t]
    [`(while (,label ,(? bexpr? b)) do ,(? stmt? s)) #t]
    ;; proc
    [`(,lc ,lr call ,p (,as ...)) #t]
    [else #f]))

;; all labels inside a statement
(define (labels s)
  (match s
    [`(,label = ,(? variable? x) ,(? aexpr? a)) (list label)]
    [`(,label SKIP) (list label)]
    [`(,(? stmt? ss) ...) (foldl (λ (s res) (append res (labels s))) '() ss)]
    [`(if (,label ,(? bexpr? b)) ,(? stmt? s1) ,(? stmt? s2))
     (cons label (append (labels s1) (labels s2)))]
    [`(while (,label ,(? bexpr? b)) do ,(? stmt? s))
     (cons label (labels s))]
    ;; proc
    [`(begin (,d* ...) (,s* ...) end)
     (set-union (foldl (λ (d res) (set-union (labels d) res)) '() d*)
                (labels s*))]
    [`(,lc ,lr call ,p (,as ...))
     `(,lc ,lr)]
    [`(,lx proc ,p (val (,xs ...) res ,y) is ,ln ,s end)
     (set-union `(,ln ,lx)
                (labels s))]))


;; blocks is set of statement or elementary blocks, of the form
;; assignment and skip
(define (block? b)
  (match b
    [`(,label = ,(? variable? x) ,(? aexpr? a)) #t]
    [`(,label ,(? bexpr? b)) #t] 
    [`(,label SKIP) #t]
    [`(,lc ,lr call ,p (,as ...)) #t]
    ;; function itself also a block
    [`(,ln ,lx is end) #t]
    [else #f]))

;; blocks : Stmt → P(Blocks)
(define (blocks st)
  (match st
    [`(,label = ,(? variable? x) ,(? aexpr? a)) (list st)]
    [`(,label SKIP) (list st)]
    ;; sequence, for here I just use list
    [`(,(? stmt? ss) ...) (foldl (λ (s res) (set-union res (blocks s))) '() ss)]
    [`(if ,eguard ,(? stmt? s1) ,(? stmt? s2))
     (set-union (list eguard)
                (blocks s1)
                (blocks s2))]
    [`(while ,eguard do ,(? stmt? s))
     (set-union (list eguard)
                (blocks s))]
    [`(begin (,d* ...) (,s* ...) end)
     (define blocks-d*
       (foldl (λ (d res) (set-union res (blocks d))) '()  d*))
     (define blocks-s*
       (blocks s*))
     (set-union blocks-s* blocks-d*)]
    [`(,lx proc ,p (val (,xs ...) res ,y) ,ln is ,s end)
     (set-add (blocks s) `(,ln ,lx is end))]
    [`(,lc ,lr call ,p (,as ...))
     (list st)]))

;; find statement by label inside a top-level state ment
(define (find-block-by-label s* l)
  (match s*
    [`(,label = ,(? variable? x) ,(? aexpr? a))
     (if (equal? label l) s* #f)]
    [`(,label SKIP) #f]
    [`(,(? stmt? ss) ...) (foldl (λ (s res) (or res (find-block-by-label s l))) #f ss)]
    [`(if (,label ,(? bexpr? b)) ,(? stmt? s1) ,(? stmt? s2))
     (if (equal? label l)
         `(,label ,b)
         (or (find-block-by-label s1 l)
             (find-block-by-label s2 l)))]
    [`(while (,label ,(? bexpr? b)) do ,(? stmt? s))
     (if (equal? label l)
         `(,label ,b)
         (find-block-by-label s l))]
    [`(begin (,d* ...) (,ss ...) end)
     (or (find-block-by-label ss l)
         (foldl (λ (d res)
                    (or (find-block-by-label d) res))
                  #f
                  d*))]
    [`(,lx proc ,p (val (,xs ...) res ,y) ,ln is ,s end)
     (or (if (equal? `(,ln ,lx) l) `(,ln ,lx is end) #f)
         (find-block-by-label s l))]
    [`(,lc ,lr call ,p (,as ...))
     (if (equal? l `(,lc ,lr))
         s*
         #f)]))


(define (find-definition-by-label d* l)
  (match d*
    [`(,lx proc ,p (val (,xs ...) res ,y) ,ln is ,s end)
     (if (equal? lx l)
         d*
         #f)]
    [`(,(? definition? ds) ...)
     (foldl (λ (d res) (or (find-definition-by-label d) res)) #f ds)]))

(define (find-definition-by-name d* name)
  (match d*
    [`(,lx proc ,p (val (,xs ...) res ,y) ,ln is ,s end)
     (if (equal? p name) d* #f)]
    [`(,(? definition? ds) ...)
     (foldl (λ (d res) (or (find-definition-by-name d) res)) #f ds)]))

;; find all call
(define (call* prog) (filter call? (blocks prog)))
