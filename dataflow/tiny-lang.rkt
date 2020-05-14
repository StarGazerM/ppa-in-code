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
    [`(,(? op-r?) ,(? aexpr? aes) ...) aes]
    [else '()]))

;; all sub arithmetic expression in a statement
(define (aexpr* st)
  (match st
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
     (set-union (aexpr-b b) (aexpr* s))]))

;; check if a variable is a free var inside a Arithmetic Expression
;; isFreeVar : Var → AExpr → Bool
(define (isFreeVar v ae)
  (match ae
    [(? variable?) (equal? v ae)]
    [`(,(? op-a?) ,(? aexpr? aes-prime) ...)
     (andmap (λ (a) (isFreeVar v a)) aes-prime)]
    [else #f]))

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
    [else #f]))

;; all labels inside a statement
(define (labels s)
  (match st
    [`(,label = ,(? variable? x) ,(? aexpr? a)) (cons label (labels a))]
    [`(,label SKIP) (list label)]
    [`(,(? stmt? ss) ...) (foldl (λ (s res) (append res (labels s))) '() ss)]
    [`(if (,label ,(? bexpr? b)) ,(? stmt? s1) ,(? stmt? s2))
     (cons label (append (labels s1) (labels s2)))]
    [`(while (,label ,(? bexpr? b)) do ,(? stmt? s))
     (cons label (labels s))]))


;; blocks is set of statement or elementary blocks, of the form
;; assignment and skip
(define (block? b)
  (match b
    [`(,label = ,(? variable? x) ,(? aexpr? a)) #t]
    [`(,label ,(? bexpr? b)) #t]
    [`(,label SKIP) #t]
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
                (blocks s))]))

;; find statement by label inside a top-level state ment
(define (find-block-by-label s* l)
  (match st
    [`(,label = ,(? variable? x) ,(? aexpr? a))
     (if (equal? label l) st #f)]
    [`(,label SKIP) #f]
    [`(,(? stmt? ss) ...) (foldl (λ (s res) (or res (find-stmt-by-label s l))) '() ss)]
    [`(if (,label ,(? bexpr? b)) ,(? stmt? s1) ,(? stmt? s2))
     (if (equal? label l)
         `(,label ,(? bexpr? b))
         (or (find-stmt-by-label s1 l)
             (find-stmt-by-label s2 l)))]
    [`(while (,label ,(? bexpr? b)) do ,(? stmt? s))
     (if (equal? label l)
         `(,label ,(? bexpr? b))
         (find-stmt-by-label s l))]))
