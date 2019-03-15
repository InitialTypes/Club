open import Library
open import Terms
open import STLC

open import Henkin.Semantics

module Henkin.LogicalPredicate where

{- Alternatively we could require P to be only given at base types:
  field P′ : ∀ P → [ atom P ] → Set
and define
  P : ∀ A → [ A ] → Set
  P (atom P) = P′ P
  P (A ⇒ B) f = ∀ x → P A x → P B (apply f x)
inductively. -}

record LogicalPredicate (H : Henkin) : Set₁ where
  open Henkin H public
  field P : ∀ A → [ A ] → Set
  field P-fun : ∀{A B} (f : [ A ⇒ B ]) → P (A ⇒ B) f → ∀ x → P A x → P B (apply f x)
  field P-ext : ∀{A B} (f : [ A ⇒ B ]) → (∀ x → P A x → P B (apply f x)) → P (A ⇒ B) f

-- 𝓟 D are the predicates on D
𝓟 : Set → Set₁
𝓟 D = D → Set

_∈_ : ∀{D} → (x : D) (D′ : 𝓟 D) → Set
x ∈ D′ = D′ x

module FundamentalLemma (H : Henkin) (L : LogicalPredicate H) where
  open LogicalPredicate L

  -- pointwise extension of P to contexts
  P* : ∀ Γ → [ Γ ]* → Set
  P* ε γ = ⊤
  P* (Γ , A) (γ , a) = P* Γ γ × P A a

  fundv : ∀{Γ A} (v : Var Γ A) {γ} → γ ∈ P* Γ → v⟨ v ⟩ γ ∈ P A
  fundv zero (γ∈R* , a∈P) = a∈P
  fundv (suc v) (γ∈P* , a∈R) = fundv v γ∈P*

  -- the "fundamental lemma"
  fund : ∀{Γ A} (t : Term Γ A) {γ} → γ ∈ P* Γ → ⟨ t ⟩ γ ∈ P A
  fund (var v) {γ} γ∈R*
    rewrite law-var v γ
            = fundv v γ∈R*
  fund (abs {Γ} {A} {B} t) {γ} γ∈R* = P-ext (⟨ abs t ⟩ γ)
    λ a a∈R → subst (P B) (sym (law-apply-abs t γ a))
                          (fund t (γ∈R* , a∈R))
  fund (app t u) {γ} γ∈R*
    rewrite law-app t u γ
            = P-fun (⟨ t ⟩ γ) (fund t γ∈R*) (⟨ u ⟩ γ) (fund u γ∈R*)
