;; data flow graph

;; Yihao Sun
;; 2020 Syracuse
#lang racket

(require "tiny-lang.rkt")

(provide (all-defined-out))
;; pure racket version

;; init function return the inital label of a statement
;; get all start point of a flow edge
;; init: Stmt → Lab
(define (init-flow stmt)
  (match stmt
    [`(,label = ,(? variable? x) ,(? aexpr? a)) label]
    [`(,label SKIP) label]
    [`(,(? stmt? stmts) ...) (init-flow (car stmts))]
    [`(if (,label ,(? bexpr? b)) ,s1 ,s2) label]
    [`(while (,label ,(? bexpr? b)) do ,(? stmt? s)) label]
    ;; procedure
    [`(,lc ,lr call ,p (,as ...)) lc]
    [`(,lx proc ,p (val (,xs ...) res ,y) ,ln is ,s end) ln]
    [`(begin (,d* ...) (,s* ...) end)
     (init-flow s*)]))

;; the end of a flow
;; final: Stmt → 𝑷(Lab)
(define (final-flow stmt)
  (match stmt
    [`(,label = ,(? variable? x) ,(? aexpr? a)) (list label)]
    [`(,label SKIP) (list label)]
    ['() '()]
    [`(,(? stmt? s)) (final-flow s)]
    [`(,(? stmt? stmts) ...) (final-flow (cdr stmts))]
    [`(if (,label ,(? bexpr? b)) ,(? stmt? s1) ,(? stmt? s2))
     (set-union (final-flow s1) (final-flow s2))]
    [`(while (,label ,(? bexpr? b)) do ,(? stmt? s))
     (list s)]
    ;; procedure
    [`(,lc ,lr call ,p (,as ...))
     (list lr)]
    [`(,lx proc ,p (val (,xs ...) res ,y) ,ln is ,s end)
     (list lx)]
    [`(begin (,d* ...) (,s* ...) end)
     (final-flow s*)]))

;; flow and reverse flow
;; flow : Stmt -> [ProcDefinition] -> 𝑷(Lab × Lab)
(define (flow stmt [d* '()])
  (match stmt
    [`(,label = ,(? variable? x) ,(? aexpr? a)) '()]
    [`(,label SKIP) '()]
    ['() '()]
    [`(,(? stmt? s)) (flow s d*)]
    [`(,(? stmt? s) ...)
     (define s1 (car s))
     (define s2 (cdr s))
     (set-union (flow s1 d*)
                (flow s2 d*)
                (remove-duplicates
                 (map (λ (l) `(,l ,(init-flow s2))) (final-flow s1))))]
    [`(if (,label ,(? bexpr? b)) ,(? stmt? s1) ,(? stmt? s2))
     (set-union (flow s1 d*)
                (flow s2 d*)
                `((,label ,(init-flow s1))
                  (,label ,(init-flow s2))))]
    [`(while (,label ,(? bexpr? b)) do ,(? stmt? s))
     (set-union (flow s d*)
                `((,label ,(init-flow s)))
                (map (λ (l) `(,l ,label)) (final-flow s)))]
    ;; procedure
    ;; (=> lc ln) is flow of calling p at lc and with ln being the entry point for procedure body
    ;; (<= lx lr) is flow of exiting p body at lx and returning to call at lr
    [`(,lc ,lr call ,p (,as ...))
     (match (find-definition-by-name d* p)
       [`(,lx proc ,p (val (,xs ...) res ,y) ,ln is ,s end)
        `((=> ,lc ,ln) (<= ,lx ,lr))]
       )]
    [`(,lx proc ,p (val (,xs ...) res ,y) ,ln is ,s end)
     (set-union (list `(,ln ,(init-flow s)))
                (flow s d*)
                (map (λ (l) `(,l ,lx)) (final-flow s)))]
    [`(begin (,d* ...) (,s* ...) end)
     (set-union (foldl (λ (d res) (set-union (flow d d*) res)) '() d*)
                (flow s* d*))]))

;; interprocedure flow
(define (inter-flow p)
  (match p
    [`(begin (,d* ...) (,s* ...) end)
     (foldl (λ (c res)
              (set-union
               res
               (match c
                 [`(,lc ,lr call ,p (,as ...))
                  (match (find-definition-by-name d* p)
                    [`(,lx proc ,p (val (,xs ...) res ,y) ,ln is ,s end)
                     (list `(,lc ,ln ,lx ,lr))])])))
            '()
            (call* p))]))

;; reverse flow
;; this is easy
(define (flowʳ stmt)
  (map reverse (flow stmt)))


;; immediate predecessor of a statement
;; this not in PPA, but used in Jeff Foster's slides
;; preds :: 𝑷(Lab × Lab) -> Lab -> 𝑷(Lab)
(define (preds graph l)
  (for/fold ([res '()])
            ([edge (in-list graph)])
    (if (equal? (second edge) l)
        (cons (first edge) res)
        res)))

;; immediate succssor of a statement
;; this not in PPA, but used in Jeff Foster's slides
;; succs ::  𝑷(Lab × Lab) -> Lab -> 𝑷(Lab)
(define (succs graph l)
  (for/fold ([res '()])
            ([edge (in-list graph)])
    (if (equal? (first edge) l)
        (cons (second edge) res)
        res)))

;; Example 2.1
(define example2-1
  `((1 = z 1)
    (while (2 (> x 0))
      do
      ((3 = z (* z y))
       (4 = x (- x 1))))))

;; flow.rkt> (flow example2-1)
;; '((1 2) (3 4) (2 3) (4 2))

(define example2-33
  '(begin ((8 proc fib (val (z u) res v) 1 is
             (if (2 (< z 3))
                 (3 = v (+ u 1))
                 ((4 5 call fib ((- z 1) u v))
                  (6 7 call fib ((- z 2) v v))))
             end))
          ((9 10 call fib (x 0 y)))
          end))
