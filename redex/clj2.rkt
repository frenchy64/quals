#lang racket

(require redex)
(require racket/random)
(require racket/format)
(require test-engine/racket-tests)
(require redex/pict)

;; for generators
(caching-enabled? #f)

(define-language Clojure
  ; simple expressions with no free variables
  (CNST ::= N O B NIL (HashMap) ERR)
  ;; expressions
  (M ::=
     CNST L LN X
     (M M ...)
     (if M M M))
  (X ::= variable-not-otherwise-mentioned)
  (ERR ::= (error any any ...))
  (L ::= (fn [X ...] M))
  (LN ::= (fn X [X ...] M))
  (FNVALUE ::= O L LN)
  (NONFNVALUE ::= B H NIL N)
  ; non-error values
  (NONERRV ::= FNVALUE NONFNVALUE)
  (V ::= NONERRV ERR)
  (H ::= (HashMap (NONERRV NONERRV) ...))
  (B ::= true false)
  (NIL ::= nil)
  (N ::= number)
  (O ::= O1 O2 O3)
  (P? ::= zero? number? boolean? nil?)
  (O1 ::= inc dec P?)
  (O2 ::= + * dissoc)
  (O3 ::= assoc get)
  ; context
  (C ::= hole (if C M M) (V ... C M ...)))

(define-language REDEX)
(define-judgment-form REDEX
  #:mode (lookup I I O)
  #:contract (lookup (any (any any) ...) any any)
  [(lookup (any_n _ ... (any any_0) _ ...) any any_0)])

(define-metafunction REDEX
  ext1 : (any (any any) ...) (any any) -> (any (any any) ...)
  [(ext1 (any_n any_0 ... (any_k any_v0) any_1 ...) (any_k any_v1))
   (any_n any_0 ... (any_k any_v1) any_1 ...)]
  [(ext1 (any_n any_0 ...) (any_k any_v1))
   (any_n (any_k any_v1) any_0 ...)])

(define-metafunction REDEX
  ext : (any (any any) ...) (any any) ... -> (any (any any) ...)
  [(ext any) any]
  [(ext any any_0 any_1 ...)
   (ext1 (ext any any_1 ...) any_0)])

(define-relation REDEX
  unique ⊆ (any ...)
  [(unique (any_!_1 ...))])

(define (remove-key H V_k)
  (list* 'HashMap
         (filter (lambda (e)
                   (not (equal? V_k (car e))))
                 (cdr H))))

(define (lookup-hash-map H V_k V_d)
  (let ([e (assv V_k (cdr H))])
    (if e
        (cadr e)
        V_d)))

;; fv
;; E -> (listof X)
;; calculates the free variables
;; that appear in a λ-calculus term
(define-metafunction Clojure
  fv : M -> (X ...)
  [(fv CNST) ()]
  [(fv X) (X)]
  [(fv (fn [X ...] M)) ,(remove* (term (X ...)) (term (fv M)))]
  [(fv (fn X_rec [X ...] M)) ,(remove* (term (X_rec X ...)) (term (fv M)))]
  [(fv (M M_args ...))
   ,(append-map (lambda (m) (term (fv ,m))) (term (M M_args ...)))])

;; fv tests
(module+ test
  ;; constants
  (test-equal (term (fv (fn [x]
                            (nil true false (HashMap)
                                 (error msg)
                                 inc
                                 +
                                 y
                                 assoc
                                 x
                                 1))))
              (term (y)))
  ;; check fv var case
  (test-equal (term (fv x))
              (term (x)))
  ;; λ case
  ;; check bound var is excluded
  (test-equal (term (fv (fn [x] (x y))))
              (term (y)))
  (test-equal (term (fv (fn rec [x] (x y))))
              (term (y)))
  ;; check fv app case
  (test-equal (term (fv (x y)))
              (term (x y))
              #:equiv set=?)
  ;; non-trivial/compound test
  (test-equal (term (fv ((fn [a] (b c))
                         (fn [d] (d e)))))
              (term (b c e))
              #:equiv set=?))

(define-judgment-form Clojure
  #:mode (δ I O)
  #:contract (δ (O V ...) V)
  [(δ (dissoc H V_k) ,(remove-key (term H) (term V_k)))]
  [(δ (assoc H V_k V_v) (ext H (V_k V_v)))]
  [(δ (get H V_k V_d) ,(lookup-hash-map (term H) (term V_k) (term V_d)))]
  [(δ (+ N_0 N_1) ,(+ (term N_0) (term N_1)))]
  [(δ (* N_0 N_1) ,(* (term N_0) (term N_1)))]
  [(δ (number? any) ,(if (number? (term any))
                         (term true)
                         (term false)))]
  [(δ (boolean? any) ,(if (or (equal? 'true (term any))
                              (equal? 'false (term any)))
                          (term true)
                          (term false)))]
  [(δ (nil? any) ,(if (equal? 'nil (term any))
                      (term true)
                      (term false)))]
  [(δ (dec N) ,(sub1 (term N)))]
  [(δ (inc N) ,(add1 (term N)))]
  [(δ (zero? N) ,(if (zero? (term N))
                     (term true)
                     (term false)))])

(define (truthy? v)
  (and (not (equal? v 'false))
       (not (equal? v 'nil))))

;; subst
(define-metafunction Clojure
  subst : M [X ↦ M] -> M
  [(subst X [X ↦ M]) M]
  [(subst X_1 [X ↦ M]) X_1]
  ;; subst X_1 to X_n
  [(subst (fn [X_1 ...] M_1) [X ↦ M])
   ,(let ([X_vs (map (lambda (x)
                       (variable-not-in (term (X M_1 M)) (term x)))
                     (term (X_1 ...)))])
      (term (fn ,X_vs
                (subst
                 (subst* M_1 ,(map (lambda (l r) (term [,l ↦ ,r]))
                                   (term (X_1 ...))
                                   X_vs))
                 [X ↦ M]))))]
  ;; subst X_rec first, then X_1 to X_n
  [(subst (fn X_rec [X_1 ...] M_1) [X ↦ M])
   ,(let* ([not-in (term (X X_rec M_1 M))]
           [X_vs (map (lambda (x)
                       (variable-not-in not-in (term x)))
                     (term (X_1 ...)))]
           [X_vrec (variable-not-in not-in (term X_rec))])
      (term (fn X_vrec
                ,X_vs
                (subst
                 (subst* M_1 ,(map (lambda (l r) (term [,l ↦ ,r]))
                                   (term (X_v X_1 ...))
                                   (cons X_vrec X_vs)))
                 [X ↦ M]))))]
  [(subst (M_1 M_2 ...) [X ↦ M])
   ((subst M_1 [X ↦ M])
    (subst M_2 [X ↦ M]) ...)])

(define-metafunction Clojure
  subst* : M ([X ↦ M] ...) -> M
  [(subst* M_1 ([X ↦ M] ...))
   ,(foldl (lambda (x_1 x_v m)
             (term (subst ,m [,x_1 ↦ ,x_v])))
           (term M_1)
           (term (X ...))
           (term (M ...)))])

;; α=?
(define-metafunction Clojure
  α=? : M M -> boolean
  [(α=? X_1 X_2) ,(equal? (term X_1) (term X_2))]
  [(α=? (fn (X_1 ...) M_1)
        (fn (X_2 ...) M_2))
   ,(and (equal? (length (term (X_1 ...)))
                 (length (term (X_2 ...))))
         (term (α=? M_1 (subst* M_2 ([X_2 ↦ X_1] ...)))))]
  [(α=? (fn X_rec1 (X_1 ...) M_1)
        (fn X_rec2 (X_2 ...) M_2))
   ,(and (equal? (length (term (X_1 ...)))
                 (length (term (X_2 ...))))
         (term (α=? M_1 (subst* M_2 ([X_rec2 ↦ X_rec1] [X_2 ↦ X_1] ...)))))]
  [(α=? (M_1l M_1r ...) (M_2l M_2r ...))
   ,(and (equal? (length (term (M_1r ...)))
                 (length (term (M_2r ...))))
         (term (α=? M_1l M_2l))
         (andmap (lambda (l r)
                   (term (α=? ,l ,r)))
                 (term (M_1r ...))
                 (term (M_2r ...))))]
  [(α=? M_1 M_2) #f])

(define (α-equal? t1 t2)
  (term (α=? ,t1 ,t2)))

;; α=? and subst tests
(module+ test
  ;; subst var tests
  (test-equal (term (subst x [x ↦ y]))
              (term y))
  (test-equal (term (subst x [y ↦ z]))
              (term x))

  ;; subst* tests
  (test-equal
   (term (subst* (fn (x) x) ([x ↦ y])))
   (term (fn (z) z))
   #:equiv α-equal?)

  (test-equal
   (term (subst (b x) (b ↦ a)))
   (term (a x)))
  (test-equal
   (term (subst* (b x) ((b ↦ a))))
   (term (a x)))
  
  ;; subst λ tests
  ;; verify substitution respects binders introducing
  ;; names being substituted for
  (test-equal
   (term (subst (fn (x) x) [x ↦ y]))
   (term (fn (z) z))
   #:equiv α-equal?)
  (test-equal
   (term (subst (fn a (x) x) [x ↦ y]))
   (term (fn b (z) z))
   #:equiv α-equal?)
  
  ;; verify substitution does not capture variables
  (test-equal
   (term (subst (fn (x) (x y)) [y ↦ (x x)]))
   (term (fn (z) (z (x x))))
   #:equiv α-equal?)

  (test-equal
   (term (subst (fn a (x) (x y)) [y ↦ (x x)]))
   (term (fn b (z) (z (x x))))
   #:equiv α-equal?)

  
  ;; subst app tests
  (test-equal (term (subst ((x y) (x y)) [x ↦ y]))
              (term ((y y) (y y))))
  
  ;; α=? var tests
  (test-equal (term (α=? x x))
              #t)
  (test-equal (term (α=? x y))
              #f)
  
  ;; α=? subst λ tests
  (test-equal (term (α=? (fn (a) (a x))
                         (fn (b) (b x))))
              #t)
  (test-equal (term (α=? (fn x (a) (a x))
                         (fn x (b) (b x))))
              #t)
  
  ;; α=? app tests
  (test-equal (term (α=? ((fn (a) (a x))
                          (fn (b) (b x)))
                         ((fn (c) (c x))
                          (fn (d) (d x)))))
              #t)
  )

;; -->v
;; Clojure reduction relation
(define -->v
  (reduction-relation
   Clojure
   #:domain M
   [--> (in-hole C ((fn (X) M_1) V_2))
        (in-hole C (subst M_1 [X ↦ V_2]))
        "β"]
   [--> (in-hole C ((fn X_rec (X ...) M_1) V_2 ...))
        (in-hole C (subst* M_1 ([X_rec ↦ (fn X_rec (X ...) M_1)]
                                [X ↦ V_2] ...)))
        "βrec"]
   [--> (in-hole C (if V_1 M_1 M_2))
        (in-hole C M_1)
        (side-condition (truthy? (term V_1)))
        "if-t"]
   [--> (in-hole C (if V_1 M_1 M_2))
        (in-hole C M_2)
        (side-condition (not (truthy? (term V_1))))
        "if-f"]
   [--> (in-hole C ERR)
        ERR
        "error"]
   ))

(module+ test
  ;; test for var (no reduction)
  (test--> -->v
           #:equiv α-equal?
           (term x))
  ;; test for lambda (no reduction)
  (test--> -->v
           #:equiv α-equal?
           (term (fn (x) x)))
  ;; β
  (test--> -->v
           #:equiv α-equal?
           (term ((fn (x) x) y))
           (term y))
  ;; β in a context
  (test--> -->v
           #:equiv α-equal?
           (term (((fn (x) x) y) z))
           (term (y z)))
  ;; η
  (test--> -->v
           #:equiv α-equal?
           (term (fn (x) (f x)))
           (term f))
  
  ;; η in a context
  (test--> -->v
           #:equiv α-equal?
           (term ((fn (x) x) (fn (x) (f x))))
           (term (fn (x) (f x)))
           (term ((fn (x) x) f)))
  ;; no η only if X ∈ fv(E)
  (test--> -->v
           #:equiv α-equal?
           (term (fn (x) ((x x) x)))))



#|

(define -->v
  (-->v/multi vρ Clojure))

(define-syntax-rule (-->v/multi vρ name . rest)
  (...
   (extend-reduction-relation
    ;; Apply
    (context-closure vρ name (hole K))
    name
    ;; Eval
    (--> ((if S_0 C_1 C_2) (frames F ...))
         (S_0 (frames (if [] C_1 C_2) F ...))
         ev-if)
  
    (--> ((V ... S C ...) (frames F ...))
         (S (frames (V ... [] C ...) F ...))
         ev-app)
   
    ; Continue
    (--> (NONERRV (frames)) NONERRV halt-value)
    (--> (ERR (frames F ...)) ERR halt-err)
  
    (--> (NONERRV (frames (if [] C_1 C_2) F ...))
         ((if NONERRV C_1 C_2) (frames F ...))
         co-if)
  
    (--> (NONERRV (frames (NONERRV_0 ... [] C_0 ...) F ...))
         ((NONERRV_0 ... NONERRV C_0 ...) (frames F ...))
         co-app)

    . rest)))
|#