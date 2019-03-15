module Terms where

data Atom : Set where
  atom_P : Atom
  atom_Q : Atom

-- A, B
data Type : Set where
  atom : Atom → Type
  _⇒_ : (A : Type) (B : Type) → Type

-- Γ, Δ, snoc-lists
data Context : Set where
  ε : Context
  _,_ : (Γ : Context) (A : Type) → Context

-- v, indices
data Var : (Γ : Context) (A : Type) → Set where
  zero : ∀{Γ A} → Var (Γ , A) A
  suc : ∀{Γ A B} (v : Var Γ A) → Var (Γ , B) A

-- t, u
data Term : (Γ : Context) (A : Type) → Set where
  var : ∀{Γ A} (v : Var Γ A) → Term Γ A
  abs : ∀{Γ A B} (t : Term (Γ , A) B) → Term Γ (A ⇒ B)
  app : ∀{Γ A B} (t : Term Γ (A ⇒ B)) (u : Term Γ A) → Term Γ B


module Renaming where
  -- (I don't require injectivity)
  _⊆_ : (Γ Δ : Context) → Set
  Γ ⊆ Δ = ∀{A} → Var Γ A → Var Δ A

  -- lifting an inclusion
  ↑⊆ : ∀{Γ Δ A} → Γ ⊆ Δ → (Γ , A) ⊆ (Δ , A)
  ↑⊆ i zero = zero
  ↑⊆ i (suc v) = suc (i v)

  -- weakening/renaming a term
  _↓_ : ∀{Γ Δ A} → (t : Term Γ A) (i : Γ ⊆ Δ) → Term Δ A
  var v   ↓ i = var (i v)
  abs t   ↓ i = abs (t ↓ ↑⊆ i)
  app t u ↓ i = app (t ↓ i) (u ↓ i)

open Renaming public

module Substitution where
  _≤_ : (Γ Δ : Context) → Set
  Γ ≤ Δ = ∀{A} → Var Γ A → Term Δ A

  -- lifting a substitution
  ↑σ : ∀{Γ Δ A} → Γ ≤ Δ → (Γ , A) ≤ (Δ , A)
  ↑σ σ zero = var zero
  ↑σ σ (suc v) = σ v ↓ suc

  -- substituting in a term
  _/_ : ∀{Γ Δ A} → (t : Term Γ A) (σ : Γ ≤ Δ) → Term Δ A
  var v   / σ = σ v
  abs t   / σ = abs (t / ↑σ σ)
  app t u / σ = app (t / σ) (u / σ)

  sub : ∀{Γ A} → (u : Term Γ A) → (Γ , A) ≤ Γ
  sub u zero = u
  sub u (suc v) = var v

  -- substituting the top-most variable by a term
  _/x←_ : ∀{Γ A B} (t : Term (Γ , A) B) (u : Term Γ A) → Term Γ B
  t /x← u = t / sub u

open Substitution public
