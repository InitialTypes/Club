open import Library
open import Terms
open import STLC

module Henkin.Semantics where

{- The following is one possible way of encoding Henkin-style models in type
theory. Using this formulation we are only able to prove soundness pointwise,
i.e. up to functional extensionality! -}

-- Agda does not currently allow recursive definitions in modules
module aux ([_] : Type → Set) where
  [_]* : (Γ : Context) → Set
  [ ε ]* = ⊤
  [ Γ , A ]* = [ Γ ]* × [ A ]

  v⟨_⟩ : ∀{Γ A} (t : Var Γ A) (γ : [ Γ ]*) → [ A ]
  v⟨ zero ⟩ = proj₂
  v⟨ suc t ⟩ = v⟨ t ⟩ ∘ proj₁

record Henkin : Set₁ where
  field [_] : (A : Type) → Set
  open aux [_] public
  field
    ⟨_⟩ : ∀{Γ A} → (t : Term Γ A) (γ : [ Γ ]*) → [ A ]
    apply : ∀{A B} → [ A ⇒ B ] → [ A ] → [ B ]
    law-var : ∀{Γ A} (v : Var Γ A) γ → ⟨ var v ⟩ γ ≡ v⟨ v ⟩ γ
    law-apply-abs : ∀{Γ A B} (t : Term (Γ , A) B) γ a →
      apply (⟨ abs t ⟩ γ) a ≡ ⟨ t ⟩ (γ , a)
    law-app : ∀{Γ A B} (t : Term Γ (A ⇒ B)) (u : Term Γ A) γ →
      ⟨ app t u ⟩ γ ≡ apply (⟨ t ⟩ γ) (⟨ u ⟩ γ)
    law-ext : ∀{A B} (f g : [ A ⇒ B ]) →
      (∀ a → apply f a ≡ apply g a) → f ≡ g

module Semantics′ (H : Henkin) where
  open Henkin H public

  sem : STLC-Semantics
  sem = record { _⊨_ = λ Γ A → [ Γ ]* → [ A ] ;
                 ⟨_⟩ = ⟨_⟩ }

  i⟨_⟩ : ∀{Γ Δ} (i : Γ ⊆ Δ) → [ Δ ]* → [ Γ ]*
  i⟨_⟩ {ε} i δ = tt
  i⟨_⟩ {Γ , A} i δ = i⟨ i ∘ suc ⟩ δ , v⟨ i zero ⟩ δ

  σ⟨_⟩ : ∀{Γ Δ} (σ : Γ ≤ Δ) → [ Δ ]* → [ Γ ]*
  σ⟨_⟩ {ε} σ δ = tt
  σ⟨_⟩ {Γ , A} σ δ = σ⟨ σ ∘ suc ⟩ δ , ⟨ σ zero ⟩ δ
