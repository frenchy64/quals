#lang racket

(require redex)
(require racket/random)

;; for generators
(caching-enabled? #f)

(define-language Clojure
  ; simple expressions that throw away their closures
  (CNST :: = X N O B NIL (HashMap) ERR)
  ;; expressions
  (M ::=
     CNST L LN
     (M M ...)
     (if M M M))
  (X ::= variable-not-otherwise-mentioned)
  (ERR ::= (error any))
  (L ::= (fn [X ...] M))
  (LN ::= (fn X [X ...] M))
  ; non-error values
  (NONERRV ::= N O (L ρ) (LN ρ) B H NIL)
  (V ::= NONERRV ERR)
  (H ::= (HashMap (NONERRV NONERRV) ...))
  (B ::= true false)
  (NIL ::= nil)
  (N ::= number)
  (O ::= O1 O2 O3)
  (O1 ::= inc dec zero? number? boolean? nil?)
  (O2 ::= + * dissoc)
  (O3 ::= assoc get)
  (ρ ::= (rho (X NONERRV) ...))
  ; serious terms S ∩ V = ∅, C = S ∪ V
  ; note: (L ρ), (LN ρ) ∉ S
  (S ::=
     (CNST ρ)
     ((M M ...) ρ)
     ((if M M M) ρ)
     (if C C C) (C C ...))
  ; domain of closures
  (C ::= V (M ρ) (if C C C) (C C ...))
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
  
   (--> (((fn [X ...] M) ρ) V ...)
        (M (ext ρ (X V) ...))
        (judgment-holds (unique (X ...)))
        β)

   (--> ((name f ((fn X_f [X ...] M) ρ)) V ...)
        (M (ext ρ (X_f f) (X V) ...))
        (judgment-holds (unique (X ...)))
        rec-β)
  
   (--> (O V ...) V_1
        (judgment-holds (δ (O V ...) V_1))
        δ)

   (--> (if V C_1 C_2) C_1
        (side-condition (truthy? (term V)))
        if-t)
   (--> (if V C_1 C_2) C_2
        (side-condition (not (truthy? (term V))))
        if-f)))

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

(define-metafunction Clojure
  injclj : M -> ς
  [(injclj M) ((M (rho)) (frames))])

(define-extended-language ClojureSpec Clojure
  (FS ::= (DefFSpec (SP ...) SP))
  (SP ::= O1)
  (C ::= .... (assert-spec C SP) (gen-spec SP))
  (CNST ::= .... (gen-spec SP))
  ;; serious expressions
  (S ::= ....
     ;; ((gen-spec SP) ρ) is here because of the above CNST extension
     ((assert-spec M SP) ρ)
     (assert-spec C SP))
  ;; frame
  (F ::= .... (assert-spec [] SP))
  (M ::= ....
     ;; (CNST ρ) is already here
     (assert-spec M SP)))

(define-extended-language ClojureSpecHOF ClojureSpec
  (SP ::= .... (FSpec (SP ...) SP) (FSpec (SP ...) SP natural)))

(define-metafunction ClojureSpec
  injcljspec : M -> ς
  [(injcljspec M) ((M (rho)) (frames))])

(define-metafunction ClojureSpecHOF
  injcljspec-hof : M -> ς
  [(injcljspec-hof M) ((M (rho)) (frames))])

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
(define-gen-spec*-ext ClojureSpecHOF gen-spec*-hof
  [(gen-spec*-hof (FSpec (SP_a ...) SP_r))
   ((fn ,(map (lambda (i) (string->symbol (string-append "x" (number->string i))))
              (range (length (term (SP_a ...)))))
        ;; TODO check arg specs
        (gen-spec*-hof SP_r))
    (rho))])

(define-syntax-rule (vρ-spec/gen-spec lang gspec* . args)
  (...
   (extend-reduction-relation
    vρ lang #:domain C
   
    (--> ((gen-spec SP) ρ) (gen-spec SP) ρ-gen-spec)
    (--> ((assert-spec M SP) ρ) (assert-spec (M ρ) SP) ρ-assert-spec)

    ;; GenSpec
    (--> (gen-spec SP) (gspec* SP) gen-spec)
   
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

    (--> (assert-spec NONERRV O1)
         (((fn [x]
               (if (O1 x)
                   x
                   (error spec-error)))
           (rho))
          NONERRV)
         assert-spec-O1)
    .
    args)))
  

(define vρ-spec
  (vρ-spec/gen-spec ClojureSpec gen-spec*))

(define-syntax-rule (-->vspec/multi vρ-spec lang . args)
  (...
   (-->v/multi
    vρ-spec lang
    ;; Eval
    (--> ((assert-spec S SP) (frames F ...))
         (S (frames (assert-spec [] SP) F ...))
         ev-assert-spec)

    ;; Continue
    (--> (NONERRV (frames (assert-spec [] SP) F ...))
         ((assert-spec NONERRV SP) (frames F ...))
         co-assert-spec)
    . args)))

(define -->vspec
  (-->vspec/multi vρ-spec ClojureSpec))
(define vρ-spec-hof
  (vρ-spec/gen-spec ClojureSpecHOF gen-spec*-hof

   ; prepare FSpec gen-count
   (--> (assert-spec (name f ((fn [X ...] M) ρ))
                     (FSpec (SP_a ...) SP_r))
        (assert-spec f
                     (FSpec (SP_a ...) SP_r ,ngenerations))
        assert-fspec-init-gen-count)

   (--> (assert-spec (name f ((fn [X ...] M) ρ))
                     (FSpec (SP_a ...) SP_r 0))
        f
        assert-fspec-stop)
 
   (--> (assert-spec (name f ((fn [X ...] M) ρ))
                     (FSpec (SP_a ...) SP_r natural))
        (((fn [y]
              ((fn [,(gensym 'do)]
                   (assert-spec y (FSpec (SP_a ...) SP_r ,(sub1 (term natural)))))
               (assert-spec (y (gen-spec SP_a) ...) SP_r)))
          (rho))
         f)
        (side-condition (< 0 (term natural)))
        assert-fspec-gen)))

(define -->vspec-hof
  (-->vspec/multi vρ-spec-hof ClojureSpecHOF))

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
(define-syntax-rule (eval-clj-traces t)
  (traces -->v (term (injclj t))))

(define-syntax-rule (eval-cljspec t)
  (apply-reduction-relation* -->vspec (term (injcljspec t))))
(define-syntax-rule (eval-cljspec-no-inject t)
  (apply-reduction-relation* -->vspec (term t)))

(define-syntax-rule (eval-cljspec-hof t)
  (apply-reduction-relation* -->vspec-hof (term (injcljspec-hof t))))
(define-syntax-rule (eval-cljspec-hof-no-inject t)
  (apply-reduction-relation* -->vspec-hof (term t)))

(define-syntax-rule (eval-cljspec-traces t)
  (traces -->vspec (term (injcljspec t))))

(define-syntax-rule (eval-cljspec-hof-traces t)
  (traces -->vspec-hof (term (injcljspec-hof t))))

(test-equal (redex-match? Clojure M (term fact-5)) #t)
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
(test-equal (eval-clj ((fn [x y] (error a)) (error c) (error b)))
            '((error c)))
(test-equal (eval-clj ((fn nme [x y] (error a)) (error c) (error b)))
            '((error c)))
(test-equal (eval-clj (zero? (error a)))
            '((error a)))
(test-equal (eval-clj (assoc 1 2 (error a)))
            '((error a)))
(test-equal (eval-clj (+ 2 (error a)))
            '((error a)))


;;spec tests
(test-equal (eval-cljspec 2)
            '(2))
(test-equal (eval-cljspec (+ 2 2))
            '(4))
(test-equal (eval-cljspec (+ 2 (error a)))
            '((error a)))
(test-equal (eval-cljspec (assert-spec 1 zero?))
            '((error spec-error)))
(test-equal (eval-cljspec (assert-spec 0 zero?))
            '(0))
(test-equal (eval-cljspec (assert-spec 0 number?))
            '(0))
(test-equal (eval-cljspec (assert-spec true number?))
            '((error spec-error)))
(test-equal (eval-cljspec (assert-spec true boolean?))
            '(true))
(test-equal (eval-cljspec (assert-spec false boolean?))
            '(false))
(test-equal (eval-cljspec (assert-spec 1 boolean?))
            '((error spec-error)))

(define (singleton-pred p l)
  (and (not (empty? l))
       (empty? (cdr l))
       (p (car l))))

;spec-hof tests
(test-equal (singleton-pred number? (eval-cljspec-hof (gen-spec number?)))
            #t)
(test-equal (singleton-pred (lambda (x) (or (equal? 'true x)
                                            (equal? 'false x)))
                            (eval-cljspec-hof (gen-spec boolean?)))
            #t)
(test-equal (singleton-pred zero?
                            (eval-cljspec-hof (gen-spec zero?)))
            #t)

(test-equal (singleton-pred number?
                            (eval-cljspec-hof ((gen-spec (FSpec () number?)))))
            #t)
(test-equal (singleton-pred number?
                            (eval-cljspec-hof ((gen-spec (FSpec (number?) number?)) 1)))
            #t)
;; TODO check arguments of generated fn's
#;(test-equal (eval-cljspec-hof ((gen-spec (FSpec (number?) number?)) nil))
            '((error spec-error)))

(test-equal (eval-cljspec-hof (assert-spec (fn [x] x) (FSpec (zero?) zero?)))
            '(((fn [x] x) (rho))))
(test-equal (eval-cljspec-hof (assert-spec (fn [x] x) (FSpec (number?) zero?)))
            '((error spec-error)))
(test-equal (eval-cljspec-hof (assert-spec (fn [x] x) (FSpec (zero?) number?)))
            '(((fn [x] x) (rho))))

(test-equal (eval-cljspec-no-inject ((assert-spec
                                      (1 (rho))
                                      number?)
                                     (frames)))
            '(1))
(test-equal (eval-cljspec-hof-no-inject ((assert-spec
                                          (1 (rho))
                                          number?)
                                         (frames)))
            '(1))