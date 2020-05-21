;; code from "Reasoned Schemer"
;; a little bit different but almost the same

#lang racket

(provide ≡ equiv
         var? var
         SUCEED FAIL
         disj₂ disj2 disj
         conj₂ conj2 conj
         neverₒ nevero
         alwaysₒ alwayso
         project
         defrel
         fresh
         reify
         condₑ conde
         run run*)
;; var is a vector
(define var? vector?)
(define var vector)

;; define some var

;; (define x (var 'x))
;; (define y (var 'y))
;; (define z (var 'z))
;; (define u (var 'u))
;; (define v (var 'v))
;; (define w (var 'w))

;; association is a pair has  var in left and right side is a list contain var
;; or a var
(define (association? a)
  (match a
    [`(,(? var? lhs) ,(? list? rhs)) (ormap var? rhs)]
    [else #f]))

;; we use substitution as our order (in lattice)
;; a substitution is a list of association which is a var pair...
(define (substitution? s)
  (andmap (λ (a)
            (match a
              [`(,(? var?) ,(? var?)) #t]
              [else #f]))
          s))

;; ... or an empty substitution
(define empty-s '())

;; produce the first association in l that has v as it's car or produces #f
(define (assv v l)
  (let/ec return
      (foldl (λ (a res)
               (if (eqv? (car a) v)
                   (return a)
                   #f))
             #f
             l)))

; lookup v in substitution return the rhs of it's association
;; if a var is walked and produce a x, we know x is fresh
(define (walk v s)
  (define a (and (var? v) (assv v s)))
  (match a
    [(? pair?) (walk (cdr a) s)]
    [else v]))

;; extend a substitution s with an association between the varible x
;; and the value v or  #f if such a extending create a cycle
(define (ext-s x v s)
  (cond
    [(occurs? x v s) #f]
    [else (cons `(,x ,v) s)]))

;; occur check
(define (occurs? x v s)
  (let ([nv (walk v s)])
    (match nv
      [(? var?) (eqv? nv x)]
      [(? pair?)
       (or (occurs? x (car nv) s)
           (occurs? x (cdr nv) s))]
      [else #f])))

;; get the minimum upper bound of a lattice
(define (unify u v s)
  (let ([nu (walk u s)]
        [nv (walk v s)])
    (cond
      [(eqv? nu nv) s]
      [(var? nu) (ext-s nu nv s)]
      [(var? nv) (ext-s nv nu s)]
      [(and (pair? nu) (pair? nv))
       (let ([ns (unify (car nu) (car nv) s)])
         (and ns
              (unify (cdr u) (cdr v) ns)))]
      [else #f])))


;; a suspension is a function take nothing and return a stream
;; racket don't have type so no predicates here...

;; a stream is a list of somethin of a suspension

;; ≡ produce a goal
;; a goal is function that except a substitution and procduce a
;; stream of substitution
(define (≡ u v)
  (λ (s)
    (let ([ns (unify u v s)])
      (if ns `(,ns) '()))))

(define equiv ≡)

;; #s
(define SUCEED
  (λ (s) `(,s)))

;; #u
(define FAIL
  (λ (s) '()))

;; disjunction is just combine the stream from the goal so both of res of goal
;; can appear in final result
(define (disj₂ g₁ g₂)
  (λ (s) (append-∞ (g₁ s) (g₂ s))))

(define disj2 disj₂)

;; append 2 streams
(define (append-∞ s-∞ t-∞)
  (cond
    [(null? s-∞) t-∞]
    [(pair? s-∞)
     (cons (car s-∞)
           (append-∞ (cdr s-∞) t-∞))]
    ;; suspension
    [else (λ () (append-∞ t-∞ (s-∞)))]))


;; never is relation produce a goal, if feed something into the goal
;; produce a suspension
(define neverₒ
  (λ (s) (λ () ((neverₒ) s))))

(define nevero neverₒ)

;; create a first empty substitution
(define (alwaysₒ)
  (λ (s)
    (λ ()
      ((disj₂ SUCEED (alwaysₒ)) s))))

(define alwayso alwaysₒ)


;; give n and stream s, craete a list of first n empty stream
(define (take-∞ n s-∞)
  (cond
    [(and n (zero? n)) '()]
    [(null? s-∞) '()]
    [(pair? s-∞)
     (cons (car s-∞)
           (take-∞ (and n (sub1 n)) (cdr s-∞)))]
    [else (take-∞ n (s-∞))]))

;; conj
(define (conj₂ g₁ g₂)
  (λ (s)
    (append-map-∞ g₂ (g₁ s))))

(define conj2 conj₂)

(define (append-map-∞ g s-∞)
  (cond
    [(null? s-∞) '()]
    [(pair? s-∞)
     (append-∞ (g (car s-∞))
                (append-map-∞ g (cdr s-∞)))]
    [else
     (λ ()
       (append-map-∞ g (s-∞)))]))

;; introduce var
;; f is a lambda expression that produce a goal
(define (call/fresh name f)
  (f (var name)))

;; until to show value
(define (reify-name n)
  (format "_~a" n))

;; walk* first walk into s by v, the keep walk in s by result of walk s
(define (walk* v s)
  (define nv (walk v s))
  (match nv
    [(? var?) nv]
    [(? pair?)
     (cons (walk* (car nv) s)
           (walk* (cdr nv) s))]
    [else nv]))

;; reification the var with result value
(define (reify-s v r)
  (define nv (walk v r))
  (match nv
    [(? var?)
     (let* ([n (length r)]
            [rn (reify-name n)])
       (cons `(,nv ,rn) r))]
    [(? pair?)
     (let ([nr (reify-s (car nv) r)])
       (reify-s (cdr nv) nr))]
    [else r]))

(define (reify v)
  (λ (s)
    (let* ([nv (walk* v s)]
           [nr (reify-s nv empty-s)])
      (walk* nv nr))))

(define (run-goal n g)
  (take-∞ n (g empty-s)))

;; some macro here

(define-syntax disj
  (syntax-rules ()
    [(disj) (disj₂ FAIL)]
    [(disj g) g]
    [(disj g₀ g ...) (disj₂ g₀ (disj g ...))]))

(define-syntax conj
  (syntax-rules ()
    [(conj) (conj₂ FAIL)]
    [(conj g) g]
    [(conj g₀ g ...) (conj₂ g₀ (conj g ...))]))

(define-syntax defrel
  (syntax-rules ()
    [(defrel (name x ...) g ...)
     (define (name x ...)
       (lambda (s)
         (lambda ()
           ((conj g ...) s))))]))

(define-syntax fresh
  (syntax-rules ()
    [(fresh () g ...) (conj g ...)]
    [(fresh (x₀ x ...) g ...)
     (call/fresh (quote x₀)
                 (λ (x₀)
                   (fresh (x ...) g ...)))]))

(define-syntax condₑ
  (syntax-rules ()
    [(condₑ (g ...) ...)
     (disj (conj g ...) ...)]))

(define-syntax conde
  (syntax-rules ()
    [(conde (g ...) ...)
     (disj (conj g ...) ...)]))

(define-syntax run
  (syntax-rules ()
    [(run n (x₀ x ...) g ...)
     (run n q (fresh (x₀ x ...)
                     (≡ `(,x₀ ,x ...) q) g ...))]
    [(run n q g ...)
     (let ([q (var (quote q))])
       (map (reify q)
            (run-goal n (conj g ...))))]))

(define-syntax run*
  (syntax-rules ()
    [(run* q g ...) (run #f q g ...)]))

;; project is similar to fresh, but bind with respect to lexial scope
(define-syntax project
  (syntax-rules ()
    [(project (x ...) g ...)
     (lambda (s)
       (let ([x (walk* x s)] ...)
         ((conj g ...) s)))]))
