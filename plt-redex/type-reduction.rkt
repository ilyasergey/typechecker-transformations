#lang racket

(require redex)

;; Syntax
(define-language λrt 
  ; Expressions
  (e n x (λ (x τ) e) (e e) (-> τ e) num)
  ; Numbers
  (n number)
  ; Contexts
  (T (T e) (τ T) (-> τ T) hole)
  ; Types
  (τ num (-> τ τ))  
  ; Variables
  (x (variable-except λ ->)))

;; Contractions
(define t-red
  (reduction-relation
   λrt
   (--> (in-hole T n)
        (in-hole T num)
        "[tc-const]")
   (--> (in-hole T (λ (x τ) e))
        (in-hole T (-> τ (subst (x τ) e)))
        "[tc-lam]")
   (--> (in-hole T ((-> τ_1 τ_2) τ_1))
        (in-hole T τ_2)
        "[tc-τβ]")))

;; Substitution does not need to be capture-avoiding 
;; in the case of λrt
(define-metafunction λrt
  subst : (x any) any -> any
  ;; 1. x_1 bound, so don't continue in λ body
  [(subst (x_1 any_1) (λ (x_1 τ_1) any_2))
   (λ (x_1 τ_1) any_2)]
  ;; 1. replace x_1 with e_1
  [(subst( x_1 any_1) x_1) any_1]
  ;; 2. x_1 and x_2 are different, so don't replace
  [(subst (x_1 any_1) x_2) x_2]
  ;; the last cases cover all other expressions
  [(subst (x_1 any_1) (any_2 ...))
   ((subst (x_1 any_1) any_2) ...)]
  [(subst (x_1 any_1) any_2) any_2])

;; type? : hybrid-expression -> boolean
;; A predicate to check if is a type
(define type? (redex-match λrt τ))

;; single-step? : expression -> boolean
(define (single-step? e)
  (= (length (apply-reduction-relation t-red e)) 1))

;; General well-formedness predicate
(define (is-ok? e)
  (or (type? e) (single-step? e)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Some examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define example-wt 
  (term (λ (y (-> num (-> num num)))
          (λ (x num) (y x)))))

(define example-ill 
  (term (λ (x (-> num num))
          (λ (y num) ((x y)
                      (λ (z num) (x z)))))))

