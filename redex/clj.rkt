#lang racket


(require redex)
(define-language Clojure
  (M ::=
     N O X L LN B NIL
     (HashMap)
     (M M ...)
     (if M M M)
     ERR)
  (X ::= variable-not-otherwise-mentioned)
  (ERR ::= (error any))
  (L ::= (fn [X ...] M))
  (LN ::= (fn X [X ...] M))
  (NONERRV ::= N O (L ρ) (LN ρ) B H NIL)
  (V ::= NONERRV ERR)
  (H ::= (HashMap (NONERRV NONERRV) ...))
  (B ::= true false)
  (NIL ::= nil)
  (N ::= number)
  (O ::= O1 O2 O3)
  (O1 ::= inc dec zero? number? boolean?)
  (O2 ::= + * dissoc)
  (O3 ::= assoc get)
  (ρ ::= (rho (X NONERRV) ...))
  ; serious terms S ∩ V = ∅, C = S ∪ V
  ; note: (L ρ), (LN ρ) ∉ S
  (S ::=
     (N ρ)
     (O ρ)
     (X ρ)
     ((M M ...) ρ)
     ((if M M M) ρ)
     (if C C C) (C C ...))
  ; domain of closures
  (C ::= V S)
  ;; continuation frames
  (K ::= (frames F ...))
  (F ::= (NONERRV ... [] C ...) (if [] C C))
  (ς ::= (C K) V))

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
  [(δ (dec N) ,(sub1 (term N)))]
  [(δ (inc N) ,(add1 (term N)))]
  [(δ (zero? N) ,(if (zero? (term N))
                     (term true)
                     (term false)))])

(define (truthy? v)
  (and (not (equal? v 'false))
       (not (equal? v 'nil))))

(define vρ
  (reduction-relation
   ;defined on the domain of closures for explicit substitutions
   Clojure #:domain C
   (--> ((if M ...) ρ) (if (M ρ) ...) ρ-if)
   (--> ((M ...) ρ) ((M ρ) ...) ρ-app)
   (--> (O ρ) O ρ-op)
   (--> (N ρ) N ρ-num)
   (--> (B ρ) B ρ-bool)
   (--> (NIL ρ) NIL ρ-nil)
   (--> (ERR ρ) ERR ρ-err)
   (--> (H ρ) H ρ-hash)
   (--> (X ρ) V
        (judgment-holds (lookup ρ X V))
        ρ-x)
  
   (--> (((fn [X ...] M) ρ) NONERRV ...)
        (M (ext ρ (X NONERRV) ...))
        (judgment-holds (unique (X ...)))
        β)

   (--> ((name f ((fn X_f [X ...] M) ρ)) NONERRV ...)
        (M (ext ρ (X_f f) (X NONERRV) ...))
        (judgment-holds (unique (X ...)))
        rec-β)
  
   (--> (O NONERRV ...) V_1
        (judgment-holds (δ (O NONERRV ...) V_1))
        δ)

   (--> (if NONERRV C_1 C_2) C_1
        (side-condition (truthy? (term NONERRV)))
        if-t)
   (--> (if NONERRV C_1 C_2) C_2
        (side-condition (not (truthy? (term NONERRV))))
        if-f)))

(define -->vς
  (extend-reduction-relation
   ;; Apply
   (context-closure vρ Clojure (hole K))
   Clojure
   ;; Eval
   (--> ((if0 S_0 C_1 C_2) (frames F ...))
        (S_0 (frames (if0 [] C_1 C_2) F ...))
        ev-if)
  
   (--> ((NONERRV ... S C ...) (frames F ...))
        (S (frames (NONERRV ... [] C ...) F ...))
        ev-app)
   
   ; Continue
   (--> (NONERRV (frames)) NONERRV halt-value)
   (--> (ERR (frames F ...)) ERR halt-err)
  
   (--> (NONERRV (frames (if0 [] C_1 C_2) F ...))
        ((if0 NONERRV C_1 C_2) (frames F ...))
        co-if)
  
   (--> (NONERRV (frames (NONERRV_0 ... [] C_0 ...) F ...))
        ((NONERRV_0 ... NONERRV C_0 ...) (frames F ...))
        co-app)))

(define-metafunction Clojure
  injclj : M -> ς
  [(injclj M) ((M (rho)) (frames))])


(define-extended-language ClojureSpec Clojure
  (FS ::= (DefFSpec (SP ...) SP))
  (SP  ::= L O1)
  ;; serious expressions
  (S ::= .... (assert-spec C SP))
  (M ::= .... (gen-spec SP) (assert-spec M SP)))

(define-extended-language ClojureSpecHOF ClojureSpec
  (SP ::= .... (FSpec (SP ...) SP) (FSpec (SP ...) SP N)))

(define-metafunction ClojureSpec
  injcljspec : M -> ς
  [(injcljspec M) ((M (rho)) (frames))])

(define-metafunction ClojureSpecHOF
  injcljspec-hof : M -> ς
  [(injcljspec-hof M) ((M (rho)) (frames))])

(define-metafunction ClojureSpecHOF
  do : M M -> M
  [(do M_1 M_2) ((fn [,(gensym 'x)]
                     M_2)
                 M_1)])

(define ngenerations 10)



(define vρ-spec
  (extend-reduction-relation
   (context-closure vρ ClojureSpec C)
   ClojureSpec
   
   (--> ((gen-spec SP) ρ) (gen-spec SP) ρ-gen-spec)
   (--> ((assert-spec M SP) ρ) (assert-spec (M ρ) S) ρ-assert-spec)
  
   ;; AssertSpec
   (--> (assert-spec ((fn [X ...] M) ρ)
                     (DefFSpec (SP_a ...) SP_r))
        ((fn [X ...]
             (assert-spec
              ((fn [X ...] M)
               (assert-spec X SP_a) ...)
              SP_r))
         ρ)
        assert-deffspec)
   ;; Treat recursive functions checked with DefFSpec
   ;; as top level mutable vars, so we spec recursive calls
   (--> (assert-spec ((fn X_n [X ...] M) ρ)
                     (DefFSpec (SP_a ...) SP_r))
        ((fn X_n [X ...]
             (assert-spec
              ((fn [X ...] M)
               (assert-spec X SP_a) ...)
              SP_r))
         ρ)
        assert-rec-deffspec)

   (--> (assert-spec NONERRV (fn [x] M))
        (if ((fn [x] M) NONERRV)
            NONERRV
            (error spec-error))
        assert-fn)
   
   (--> (assert-spec NONERRV O1)
        (if (O1 NONERRV)
            NONERRV
            (error spec-error))
        assert-O1)))

;(define -->vspec
;  (extend-reduction-relation
;   ;; Apply
;   (context-closure vρ-spec ClojureSpec (hole K))
;   ClojureSpec
;
;   ;; Eval
;   (--> ((assert-spec S SP) (frames F ...))
;        (S (frames (assert-spec [] SP) F ...)))
;
;   ;; Continue
;   (--> (NONERRV (frames (assert-spec [] SP) F ...))
;        ((assert-spec NONERRV SP) (frames F ...)))))

;(define vρ-spec-hof
;  (extend-reduction-relation
;   (context-closure vρ-spec ClojureSpecHOF C)
;   ClojureSpecHOF
;
;   ; prepare FSpec gen-count
;   (--> (assert-spec ((fn [X ...] M) ρ)
;                     (FSpec (SP_a ...) SP_r))
;        (assert-spec ((fn [X ...] M) ρ)
;                     (FSpec (SP_a ...) SP_r ,ngenerations))
;        assert-fspec-init-gen-count)
;
;   (--> (assert-spec ((fn [X ...] M) ρ)
;                     (FSpec (SP_a ...) SP_r 0))
;        ((fn [X ...] M) ρ)
;        assert-fspec-stop)
; 
;   (--> (assert-spec ((fn [X ...] M) ρ)
;                     (FSpec (SP_a ...) SP_r N))
;        (((fn [y]
;              (do (assert-spec
;                   (y (gen-spec SP_a) ...)
;                   SP_r)
;                (assert-spec y (FSpec (SP_a ...) SP_r ,(sub1 (term N))))))
;          (rho))
;         ((fn [X ...] M) ρ))
;        (side-condition (< 0 (term N)))
;        assert-fspec-gen)))

;(define -->vρ-spec-hof
;  (extend-reduction-relation
;   ;; Apply
;   (context-closure -->vspec ClojureSpecHOF (hole K))
;   ClojureSpecHOF))

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

(define-syntax-rule (eval-clj t)
  (apply-reduction-relation* -->v (term (injclj t))))
;
;(define-syntax-rule (eval-cljspec t)
;  (apply-reduction-relation* -->vspec (term (injcljspec t))))
;
;(define-syntax-rule (eval-cljspec-hof t)
;  (apply-reduction-relation* -->vspec-hof (term (injcljspec-hof t))))
;
;(define-syntax-rule (eval-cljspec-traces t)
;  (traces -->vspec (term (injcljspec t))))

;(test-equal (redex-match? Clojure M (term fact-5)) #t)
;(test-equal (eval-clj true)
;            '(true))
;(test-equal (eval-clj (if (zero? 0) 0 1))
;            '(0))
;(test-equal (eval-clj (if (zero? 1) 0 1))
;            '(1))
;(test-equal (eval-clj ((fn [x] 5) 1))
;            '(5))
;(test-equal (eval-clj fact-5)
;            '(120))
;(test-equal (eval-clj (HashMap))
;            '((HashMap)))
;(test-equal (eval-clj (assoc (HashMap) 0 1))
;            '((HashMap (0 1))))
;(test-equal (eval-clj (get (assoc (HashMap) 0 1) 0 nil))
;            '(1))
;(test-equal (eval-clj (get (assoc (HashMap) 0 1) 1 nil))
;            '(nil))
;(test-equal (eval-clj (get (dissoc (assoc (HashMap) 0 1) 0) 0 nil))
;            '(nil))
;
;(test-equal (eval-clj (def/fact 5))
;            '(120))
;(test-equal (eval-clj (error a))
;            '((error a)))
;(test-equal (eval-clj (if (error a) 0 1))
;            '((error a)))
;(test-equal (eval-clj (if 0 (error a) (error b)))
;            '((error a)))
;(test-equal (eval-clj (if nil (error a) (error b)))
;            '((error b)))
;(test-equal (eval-clj ((fn [x] (error a)) 1))
;            '((error a)))
;(test-equal (eval-clj ((fn [x] (error a)) (error b)))
;            '((error b)))
;(test-equal (eval-clj ((fn nme [x] (error a)) 1))
;            '((error a)))
;(test-equal (eval-clj ((fn nme [x] (error a)) (error b)))
;            '((error b)))
;(test-equal (eval-clj (zero? (error a)))
;            '((error a)))
;(test-equal (eval-clj (assoc 1 2 (error a)))
;            '((error a)))
;(test-equal (eval-clj (+ 2 (error a)))
;            '((error a)))
;
;;;spec tests
;(test-equal (eval-cljspec (+ 2 (error a)))
;            '((error a)))
;(test-equal (eval-cljspec (assert-spec 1 zero?))
;            '((error spec-error)))
;(test-equal (eval-cljspec (assert-spec 0 zero?))
;            '(0))
;(test-equal (eval-cljspec (assert-spec 0 number?))
;            '(0))
;(test-equal (eval-cljspec (assert-spec true number?))
;            '((error spec-error)))
;(test-equal (eval-cljspec (assert-spec true boolean?))
;            '(true))
;(test-equal (eval-cljspec (assert-spec false boolean?))
;            '(false))
;(test-equal (eval-cljspec (assert-spec 1 boolean?))
;            '((error spec-error)))
;
;;spec-hof tests
;(test-equal (eval-cljspec-hof (do 1 2))
;            '(2))
;(test-equal (eval-cljspec-hof (assert-spec (((fn (x) x) (rho)) (gen-spec number?))))
;            '(0))
;(test-equal (eval-cljspec-hof (assert-spec (fn [x] x) (FSpec (number?) zero?)))
;            '(0))
