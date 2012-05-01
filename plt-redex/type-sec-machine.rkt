#lang racket

(require redex)

;; Syntax
(define-language λsec
  ; Expressions
  (e n x (λ (x τ) e) (e e))
  ; Numbers
  (n number)
  ; Types
  (τ num (-> τ τ))
  ; Environments
  (E ((x τ) ...))
  ; Variables
  (x variable-not-otherwise-mentioned)
  ; Result stacks
  (S (τ S) nil)
  ; Control elements
  (c e (Lam τ S) (Fun e) (Arg τ_1 τ_2))
  ; Control stacks
  (C (c C) nil)
  ; States
  (ξ (S E C)))

;; Small-step abstract machine
(define t-sec
  (reduction-relation
   λsec #:domain ξ
   (--> (S E (n C))
        ((num S) E C)
        "[num]")
   (--> (S E (x C))
        (((env-lookup E x) S) E C)
        "[var]")
   (--> (S E ((λ (x τ) e) C))
        (nil (env-extend E (x τ)) (e ((Lam τ S) C)))
        "[lam]")
   (--> (S E ((e_1 e_2) C))
        (S E (e_1 ((Fun e_2) C)))
        "[app]")
   (--> ((τ_2 S) E ((Lam τ_1 S_1) C))
        (((-> τ_1 τ_2) S_1) E C)
        "[t-lam]")
   (--> (((-> τ_1 τ_2) S) E ((Fun e_2) C))
        (((-> τ_1 τ_2) S) E (e_2 ((Arg τ_1 τ_2) C)))
        "[t-fun]")
   (--> ((τ_1 (any S)) E ((Arg τ_1 τ_2) C))
        ((τ_2 S) E C)
        "[t-arg]")))

;; Environment lookup
(define-metafunction λsec
  env-lookup : E x -> τ
  [(env-lookup ((x τ) (x_1 τ_1) ...) x) τ]
  [(env-lookup ((x_1 τ_1) (x_2 τ_2) ...) x)
   (env-lookup ((x_2 τ_2) ...) x)])

;; Environment extension
(define-metafunction λsec
  env-extend : E (x τ) -> E
  [(env-extend ((x_1 τ_1) ...) (x τ))
   ((x τ) (x_1 τ_1) ...)])

;; Inject expression into a machine state
(define-metafunction λsec
  inject : e -> ξ
  [(inject e) (nil () (e nil))])

;; single-step? : expression -> boolean
(define (single-step? s)
  (= (length (apply-reduction-relation t-sec s)) 1))

;; final-state? : state -> boolean
(define (final-state? ξ)
  (eq? 'nil (caddr ξ)))

;; General well-formedness predicate
(define (is-ok? ξ)
  (or (final-state? ξ) (single-step? ξ)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Some examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define example-wt 
  (term (inject (λ (y (-> num (-> num num)))
                  (λ (x num) (y x))))))

(define example-ill 
  (term (inject (λ (x (-> num num))
                  (λ (y num) ((x y) 
                              (λ (z num) (x z))))))))



(traces t-red example-ill
        #:pred is-ok?)
