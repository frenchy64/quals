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
  (CNST ::= N O B NIL H ERR)
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
  (C ::= hole (if C M M) (NONERRV ... C M ...)))

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
  #:contract (δ (O NONERRV ...) V)
  ;; TODO dynamic checks for map-ops
  [(δ (dissoc H V_k) ,(remove-key (term H) (term V_k)))]
  [(δ (assoc H V_k V_v) (ext H (V_k V_v)))]
  [(δ (get H V_k V_d) ,(lookup-hash-map (term H) (term V_k) (term V_d)))]
  [(δ (+ any_0 any_1) ,(cond
                         [(redex-match? Clojure (N_0 N_1) (term (any_0 any_1)))
                          (+ (term any_0) (term any_1))]
                         [else (term (error "Bad arguments to +" any_0 any_1))]))]
  [(δ (* any_0 any_1) ,(cond
                         [(redex-match? Clojure (N_0 N_1) (term (any_0 any_1)))
                          (* (term any_0) (term any_1))]
                         [else (term (error "Bad arguments to *" any_0 any_1))]))]
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
  [(δ (dec any) ,(cond
                   [(redex-match? Clojure N (term any))
                    (sub1 (term any))]
                   [else (term (error "Bad arguments to dec" any))]))]
  [(δ (inc any) ,(cond
                   [(redex-match? Clojure N (term any))
                    (add1 (term any))]
                   [else (term (error "Bad arguments to inc" any))]))]
  [(δ (zero? any) ,(cond
                     [(redex-match? Clojure N (term any))
                      (if (zero? (term any))
                          (term true)
                          (term false))]
                     [else (term (error "Bad arguments to zero?"))]))]
  
  )

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
      (term (fn ,X_vrec
                ,X_vs
                (subst
                 (subst* M_1 ,(map (lambda (l r) (term [,l ↦ ,r]))
                                   (term (X_rec X_1 ...))
                                   (cons X_vrec X_vs)))
                 [X ↦ M]))))]
  [(subst (M_1 M_2 ...) [X ↦ M])
   ((subst M_1 [X ↦ M])
    (subst M_2 [X ↦ M]) ...)]
  [(subst (if M_0 M_1 M_2) [X ↦ M])
   (if (subst M_0 [X ↦ M])
       (subst M_1 [X ↦ M])
       (subst M_2 [X ↦ M]))]
  [(subst CNST [X ↦ M]) CNST])

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
  [(α=? V V) #t]
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
   [--> (in-hole C X)
        (error unknown-variable X)
        x-error]
   [--> (NONFNVALUE NONERRV ...) (error bad-application)
        β-non-function]

   [--> (in-hole C ((fn (X ...) M) NONERRV ...))
        (in-hole C (subst* M ([X ↦ NONERRV] ...)))
        (judgment-holds (unique (X ...)))
        (side-condition (equal? (length (term (X ...)))
                                (length (term (NONERRV ...)))))

        β]
   [--> (in-hole C ((fn [X ...] M) NONERRV ...))
        (error argument-mismatch
               ,(string-append
                 "Expected " (~a (length (term (X ...))))
                 " arguments, but found "
                 (~a (length (term (NONERRV ...)))))
               ,(string-append
                 "Form: " (~a (list* (term (fn [X ...] M))
                                     (term (NONERRV ...))))))
        (judgment-holds (unique (X ...)))
        (side-condition (not (equal? (length (term (X ...)))
                                     (length (term (NONERRV ...))))))
        β-mismatch]

   [--> (in-hole C ((fn X_rec [X ...] M) NONERRV ...))
        (in-hole C (subst* M ([X_rec ↦ (fn X_rec [X ...] M)]
                              [X ↦ NONERRV] ...)))
        (judgment-holds (unique (X_rec X ...)))
        (side-condition (equal? (length (term (X ...)))
                                (length (term (NONERRV ...)))))

        rec-β]
   [--> (in-hole C ((name f (fn X_f [X ...] M)) NONERRV ...))
        (error argument-mismatch
               ,(string-append
                 "Expected " (~a (length (term (X ...))))
                 " arguments, but found "
                 (~a (length (term (NONERRV ...)))))
               ,(string-append
                 "Form: " (~a (list* (term (fn [X ...] M))
                                     (term (NONERRV ...))))))
        (side-condition (not (equal? (length (term (X ...)))
                                     (length (term (NONERRV ...))))))
        rec-β-mismatch]

   [--> (in-hole C (if NONERRV M_1 M_2))
        (in-hole C M_1)
        (side-condition (truthy? (term NONERRV)))
        if-t]
   [--> (in-hole C (if NONERRV M_1 M_2))
        (in-hole C M_2)
        (side-condition (not (truthy? (term NONERRV))))
        if-f]
   [--> (in-hole C (O NONERRV ...))
        (in-hole C V_1)
        (judgment-holds (δ (O NONERRV ...) V_1))
        δ]
   [--> (in-hole C ERR)
        ERR
        ;; prevent infinite top expansions of top-level errors
        (side-condition (not (equal? (term hole) (term C))))
        error]))

(module+ test
  ;; test for lambda (no reduction)
  (test--> -->v
           #:equiv α-equal?
           (term (fn (x) x)))
  ;; β
  (test--> -->v
           #:equiv α-equal?
           (term ((fn (x) x) 1))
           (term 1))
  ;; β in a context
  (test--> -->v
           #:equiv α-equal?
           (term (((fn (x) x) (fn (x) x)) 1))
           (term ((fn (x) x) 1))))


(define-syntax-rule (clj/def defname name args body)
  (define-term defname
    (fn name args body)))

(clj/def def/fact
         fact [n]
         (if (zero? n)
             1
             (* n (fact (dec n)))))

(define-term fact-5
  ((fn fact [n]
       (if (zero? n)
           1
           (* n (fact (dec n)))))
   5))

(define-extended-language ClojureSpec Clojure
  (FS ::= (DefFSpec (SP ...) SP))
  ;TODO blame paths
  (SP ::= P?)
  (C ::= .... (assert-spec C SP))
  (CNST ::= .... (gen-spec SP))
  (M ::= .... (assert-spec M SP)))

(define ngenerations 10)
(define min-random-int -2000)
(define max-random-int 2000)

(define (random-int)
  (random min-random-int max-random-int))

;; not defined in ClojureSpecHOF because we cannot
;; generate FSpec's (yet)
(define-syntax-rule (define-gen-spec*-ext lang name . args)
  (...
   (define-metafunction lang
     name : SP -> V
     [(name number?) ,(random-int)]
     [(name zero?) 0]
     [(name boolean?) ,(random-ref '(true false))]
     [(name nil?) nil]
     . args)))

(define-gen-spec*-ext ClojureSpec gen-spec*)



(define-syntax-rule (-->vspec/multi lang gspec* . args)
  (...
   (extend-reduction-relation
    -->v lang
    #:domain M

    ;; GenSpec
    (--> (in-hole C (gen-spec SP))
         (in-hole C (gspec* SP))
         gen-spec)
   
    ;; AssertSpec
    (--> (in-hole C (assert-spec (fn [X ...] M)
                                 (DefFSpec (SP_a ...) SP_r)))
         (in-hole C (fn [X ...]
                        (assert-spec
                         ((fn [X ...] M)
                          (assert-spec X SP_a) ...)
                         SP_r)))
         assert-deffspec)
    ;; Treat recursive functions checked with DefFSpec
    ;; as top level mutable vars, so we spec recursive calls
    (--> (in-hole C (assert-spec (fn X_n [X ...] M)
                                 (DefFSpec (SP_a ...) SP_r)))
         (in-hole C (fn X_n [X ...]
                        (assert-spec
                         ((fn [X ...] M)
                          (assert-spec X SP_a) ...)
                         SP_r)))
         assert-rec-deffspec)

    (--> (in-hole C (assert-spec NONERRV P?))
         (in-hole C
                  (if (P? NONERRV)
                      NONERRV
                      (error spec-error
                             ,(string-append
                               "Spec violation: "
                               "Expected spec " (~a (term P?))
                               ", actual value " (~a (term NONERRV))))))
         assert-spec-P?)
    .
    args)))

(define -->vspec
  (-->vspec/multi ClojureSpec gen-spec*))

(define-extended-language ClojureSpecHOF ClojureSpec
  (SP ::= .... (FSpec (SP ...) SP) (FSpec (SP ...) SP natural)))

(define-gen-spec*-ext ClojureSpecHOF gen-spec*-hof
  [(gen-spec*-hof (FSpec (SP_a ...) SP_r))
   (fn ,(map (lambda (i) (string->symbol (string-append "x" (number->string i))))
             (range (length (term (SP_a ...)))))
       ;; TODO check arg specs
       (gen-spec*-hof SP_r))])

(define -->vspec-hof
  (-->vspec/multi
   ClojureSpecHOF gen-spec*-hof
   ; prepare FSpec gen-count
   (--> (in-hole C (assert-spec NONERRV
                                (FSpec (SP_a ...) SP_r)))
        (in-hole C (assert-spec NONERRV
                                (FSpec (SP_a ...) SP_r ,ngenerations)))
        assert-fspec-init-gen-count)

   (--> (in-hole C
                 (assert-spec (name f (fn [X ...] M))
                              (FSpec (SP_a ...) SP_r 0)))
        (in-hole C f)
        assert-fspec-stop)
 
   (--> (in-hole C (assert-spec (name f (fn [X ...] M))
                                (FSpec (SP_a ...) SP_r natural)))
        (in-hole C
                 ((fn [,(gensym 'do)]
                      (assert-spec f (FSpec (SP_a ...) SP_r ,(sub1 (term natural)))))
                  (assert-spec (f (gen-spec SP_a) ...) SP_r)))
        (side-condition (< 0 (term natural)))
        assert-fspec-gen)

   (--> (in-hole C (assert-spec (name f (fn nme [X ...] M))
                                (FSpec (SP_a ...) SP_r natural)))
        (in-hole C ((fn [,(gensym 'do)]
                        (assert-spec f (FSpec (SP_a ...) SP_r ,(sub1 (term natural)))))
                    (assert-spec (f (gen-spec SP_a) ...) SP_r)))
        (side-condition (< 0 (term natural)))
        assert-rec-fspec-gen)

   (--> (in-hole C (assert-spec NONFNVALUE
                                (FSpec (SP_a ...) SP_r natural)))
        (error spec-error
               ,(string-append
                 "Spec expected a function but found " (~a (term NONFNVALUE))))
        assert-fspec-non-function)))

(define-syntax-rule (eval-clj t)
  (apply-reduction-relation* -->v (term t)))
(define-syntax-rule (eval-clj-no-inject t)
  (apply-reduction-relation* -->v (term t)))
(define-syntax-rule (eval-clj-traces t)
  (traces -->v (term t)))

(define-syntax-rule (eval-cljspec t)
  (apply-reduction-relation* -->vspec (term t)))

(define-syntax-rule (eval-cljspec-no-inject t)
  (apply-reduction-relation* -->vspec (term t)))

(define-syntax-rule (eval-cljspec-traces t)
  (traces -->vspec (term t)))

(define-syntax-rule (eval-cljspec-hof t)
  (apply-reduction-relation* -->vspec-hof (term t)))
(define-syntax-rule (eval-cljspec-hof-no-inject t)
  (apply-reduction-relation* -->vspec-hof (term t)))
(define-syntax-rule (eval-cljspec-hof-traces t)
  (traces -->vspec-hof (term t)))

(define (singleton-pred p l)
  (and (not (empty? l))
       (empty? (cdr l))
       (p (car l))))

(define (singleton-error? p l)
  (singleton-pred (lambda (x)
                    (and (list? x)
                         (<= 2 (length x))
                         (equal? 'error (first x))
                         (p (second x))))
                  l))

(define (singleton-spec-error? l)
  (singleton-error? (lambda (x) (equal? 'spec-error x))
                    l))
(define (singleton-arg-mismatch-error? l)
  (singleton-error? (lambda (x) (equal? 'argument-mismatch x))
                    l))
(define (singleton-unknown-var-error? l)
  (singleton-error? (lambda (x) (equal? 'unknown-variable x))
                    l))

(test-equal (redex-match? Clojure M (term fact-5)) #t)
#| ;; FIXME uncomment
(test-equal (redex-match? ClojureSpecHOF C
                          (term (assert-spec
                                 ((y (gen-spec number?))
                                  (rho (y ((fn (x) x) (rho)))))
                                 zero?)))
            #t)
(test-equal (redex-match? ClojureSpecHOF S
                          (term ((y (gen-spec number?))
                                  (rho (y ((fn (x) x) (rho)))))))
            #t)
(test-equal (redex-match? ClojureSpecHOF ((assert-spec S SP) (frames F ...))
                          (term ((assert-spec
                                  ((y (gen-spec number?)) (rho (y ((fn (x) x) (rho)))))
                                  zero?)
                                 (frames
                                  (((fn
                                     (do3460218)
                                     (assert-spec y (FSpec (number?) zero? 9)))
                                    (rho (y ((fn (x) x) (rho)))))
                                   ())))))
            #t)
|#


(test-equal (eval-clj true)
            '(true))
(test-equal (eval-clj (if (zero? 0) 0 1))
            '(0))
(test-equal (eval-clj (if (zero? 1) 0 1))
            '(1))
(test-equal (eval-clj ((fn [x] 5) 1))
            '(5))
(test-equal (eval-clj fact-5)
            '(120))
(test-equal (eval-clj (inc 1))
            '(2))
(test-equal (eval-clj (HashMap))
            '((HashMap)))
(test-equal (eval-clj (assoc (HashMap) 0 1))
            '((HashMap (0 1))))
(test-equal (eval-clj (get (assoc (HashMap) 0 1) 0 nil))
            '(1))
(test-equal (eval-clj (get (assoc (HashMap) 0 1) 1 nil))
            '(nil))
(test-equal (eval-clj (get (dissoc (assoc (HashMap) 0 1) 0) 0 nil))
            '(nil))

(test-equal (eval-clj (def/fact 5))
            '(120))
(test-equal (eval-clj (error a))
            '((error a)))
(test-equal (eval-clj (if (error a) 0 1))
            '((error a)))
(test-equal (eval-clj (if 0 (error a) (error b)))
            '((error a)))
(test-equal (eval-clj (if nil (error a) (error b)))
            '((error b)))
(test-equal (eval-clj ((fn [x] (error a)) 1))
            '((error a)))
(test-equal (eval-clj ((fn [x] (error a)) (error b)))
            '((error b)))
(test-equal (eval-clj ((fn nme [x] (error a)) 1))
            '((error a)))
(test-equal (eval-clj ((fn nme [x] (error a)) (error b)))
            '((error b)))
(test-equal (eval-clj ((fn [x y] (error a))
                       (error c)
                       (error b)))
            '((error c)))
(test-equal (eval-clj ((fn nme [x y] (error a)) (error c) (error b)))
            '((error c)))
(test-equal (eval-clj (zero? (error a)))
            '((error a)))
(test-equal (eval-clj (assoc 1 2 (error a)))
            '((error a)))
(test-equal (eval-clj (+ 2 (error a)))
            '((error a)))
(test-equal (singleton-arg-mismatch-error?
             (eval-clj ((fn [] 1) 1)))
            #t)
(test-equal (singleton-arg-mismatch-error?
             (eval-clj ((fn nme [] 1) 1)))
            #t)
(test-equal (singleton-arg-mismatch-error?
             (eval-clj ((fn [x] 1))))
            #t)
(test-equal (singleton-arg-mismatch-error?
             (eval-clj ((fn nme [x] 1))))
            #t)

(test-equal (singleton-unknown-var-error?
             (eval-clj x))
            #t)

(test-equal (eval-clj (1 2))
            '((error bad-application)))

;;spec tests
(test-equal (eval-cljspec 2)
            '(2))
(test-equal (eval-cljspec (+ 2 2))
            '(4))
(test-equal (eval-cljspec (+ 2 (error a)))
            '((error a)))
(test-equal (singleton-spec-error? (eval-cljspec (assert-spec 1 zero?)))
            #t)
(test-equal (eval-cljspec (assert-spec 0 zero?))
            '(0))
(test-equal (eval-cljspec (assert-spec 0 number?))
            '(0))
(test-equal (singleton-spec-error? (eval-cljspec (assert-spec true number?)))
            #t)
(test-equal (eval-cljspec (assert-spec true boolean?))
            '(true))
(test-equal (eval-cljspec (assert-spec false boolean?))
            '(false))
(test-equal (singleton-spec-error? (eval-cljspec (assert-spec 1 boolean?)))
            #t)


;spec-hof tests
(test-equal (singleton-pred number? (eval-cljspec-hof (gen-spec number?)))
            #t)
(test-equal (singleton-pred (lambda (x) (or (equal? 'true x)
                                            (equal? 'false x)))
                            (eval-cljspec-hof (gen-spec boolean?)))
            #t)
(test-equal (singleton-pred (lambda (x) (and (number? x)
                                             (zero? x)))
                            (eval-cljspec-hof (gen-spec zero?)))
            #t)

(test-equal (singleton-pred number?
                            (eval-cljspec-hof ((gen-spec (FSpec () number?)))))
            #t)
(test-equal (singleton-pred number?
                            (eval-cljspec-hof ((gen-spec (FSpec (number?) number?)) 1)))
            #t)
;; TODO check arguments of generated fn's
#;(test-equal (singleton-spec-error? (eval-cljspec-hof ((gen-spec (FSpec (number?) number?)) nil)))
               #t)

(test-equal (eval-cljspec-hof (assert-spec (fn [x] x) (FSpec (zero?) zero?)))
            '((fn [x] x)))
(test-equal (singleton-spec-error?
             (eval-cljspec-hof (assert-spec (fn [x] x) (FSpec (number?) zero?))))
            #t)
(test-equal (eval-cljspec-hof (assert-spec (fn [x] x) (FSpec (zero?) number?)))
            '((fn [x] x)))

(test-equal (eval-cljspec-no-inject (assert-spec
                                      1
                                      number?))
            '(1))




; ifn? test for functions
(test-equal (singleton-spec-error? (eval-cljspec-hof (assert-spec 1 (FSpec () number?))))
            #t)
; mismatch between FSpec arg count and actual count
;; removed `assert-fspec-gen-arg-mismatch`, so not a relevant test
#;(test-equal (singleton-spec-error? (eval-cljspec-hof (assert-spec (fn [x] x) (FSpec () number?))))
            #t)
(test-equal (singleton-arg-mismatch-error? (eval-cljspec-hof (assert-spec (fn [x] x) (FSpec () number?))))
            #t)


(define-syntax-rule (check-compatible-result speclang orig-clj orig-cljspec eclj ecljspec)
  (...
   (begin
    (unless (redex-match? Clojure V eclj)
      (error "Clojure evaluation did not fully reduce"
             'original-form
             orig-clj
             'stuck-form
             eclj))
    (unless (redex-match? speclang V ecljspec)
      (error (string-append
              "ClojureSpec evaluation did not fully reduce\n"
              "Original-form: " (~a orig-cljspec) "\n"
              
              "Stuck-form: " (~a ecljspec))))
    (cond
      ;; exactly the same output
      [(equal? eclj ecljspec) #t]
      ;; throws a spec error
      [(redex-match? speclang (error spec-error any ...) ecljspec) #t]
      ;; throws a different kind of error than Clojure
      [(and (redex-match? Clojure ERR eclj)
            (redex-match? speclang ERR ecljspec)) #t]
      ;; spec throws a non-spec error where Clojure returns a value
      [else (error (string-append
                    "ClojureSpec evaluation returned a different value than Clojure\n"
                    "Original-clj: " (~a orig-clj)
                   "\nOriginal-clj-spec: " (~a orig-cljspec)
                   "\nclj-value: " (~a eclj)
                   "\ncljspec-value: " (~a ecljspec)))]))))

;; check that errors are actually caught and thrown
(check-error
 (check-compatible-result ClojureSpecHOF
                          (term (fn () 1))
                          (term (assert-spec (fn () 1) (FSpec (number?) zero?)))
                          '(fn () 1)
                          '(error argument-mismatch "Expected 0 arguments, but found 1" "Form: ((fn () 1) 1771)")))



(define-syntax-rule (check-Clojure-ClojureSpec-compat* speclang eval-cljspec nforms nspecs)
  (begin
    (for/list ([i (in-range nforms)]
               [j (in-range nspecs)])
      (let* ([ct (generate-term Clojure M #:i-th (* 200 i))]
             [sp (generate-term speclang SP #:i-th (+ i j))]
             [orig-clj ct]
             [orig-cljspec (term (assert-spec ,ct ,sp))]
             [esclj (eval-clj ,orig-clj)]
             [escljspec (eval-cljspec ,orig-cljspec)]
             [eclj (if (equal? 1 (length esclj))
                       (first esclj)
                       (error "Multiple results from Clojure eval"
                              esclj))]
             [ecljspec (if (equal? 1 (length escljspec))
                           (first escljspec)
                           (error "Multiple results from ClojureSpec eval"
                                  escljspec))])
        (check-compatible-result
         speclang
         orig-clj
         orig-cljspec
         eclj
         ecljspec)))
    #f))

(define (check-Clojure-ClojureSpec-compat nforms nspecs)
  (check-Clojure-ClojureSpec-compat* ClojureSpec eval-cljspec nforms nspecs))

#; (check-Clojure-ClojureSpec-compat 1000 1000)
#; (check-Clojure-ClojureSpecHOF-compat 1000 1000)
(define (check-Clojure-ClojureSpecHOF-compat nforms nspecs)
  (check-Clojure-ClojureSpec-compat* ClojureSpecHOF eval-cljspec-hof nforms nspecs))

; the counter-example
(test-equal (eval-cljspec-hof (assert-spec (fn [x] (if (zero? x) nil (error missiles-launched)))
                                           (FSpec (number?) nil?)))
            '((error missiles-launched)))

(test-equal (eval-clj (fn [x] (if (zero? x) nil (error missiles-launched))))
            '((fn [x] (if (zero? x) nil (error missiles-launched)))))
