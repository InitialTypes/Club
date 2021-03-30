module Farmer where

open import Data.List.Membership.Propositional

open import STLC

infix 8 _⊩_

data _⊩_ (Φ : FormCtx Γ) : Form Γ → Set where
  Ass : t ∈ Φ → Φ ⊩ t

  R : Φ ⊩ t `= u → Φ ⊩ ψ [ t ]
    --------------------------
    →       Φ ⊩ ψ [ u ]

  A1 : Φ ⊩ `∀ ⋆ ⇒ ⋆ ﹒ v0 · T ∧ v0 · F ⇔ `∀ ⋆ ﹒ v1 · v0

  A2 : Φ ⊩ `∀ a ﹒ `∀ a ﹒ v1 `= v0 `⇒ `∀ a ⇒ ⋆ ﹒ v0 · v2 ⇔ v0 · v1

  A3 : Φ ⊩ `∀ a ⇒ b ﹒ `∀ a ⇒ b ﹒ v1 `= v0 ⇔ `∀ a ﹒ v2 · v0 `= v1 · v0

  A4 : Φ ⊩ (`λ t) · u `= t [ u ]

T-true : Φ ⊩ T
T-true = R {ψ = v0 `= `λ v0} (A4 {t = v0} {u = `λ v0}) {!A4!}

-- truth-lemma : Φ ⊩ eq ψ T → Φ ⊩ ψ 
-- truth-lemma = {!!}

-- `∀E :  Φ ⊩ `∀ ψ → Φ ⊩ ψ [ t ]
-- `∀E p = {!!}

-- ∧E₁ :  Φ ⊩ φ ∧ ψ → Φ ⊩ φ
-- ∧E₁ p = {!!}

-- LEM : Φ ⊩ φ ∨ ¬ φ
-- LEM = {!!}

-- I : Φ ⊩ φ `⇒ φ
-- I = {!!}

-- eq-refl : ∀ (t : Γ ⊢ a) → Φ ⊩ eq t t
-- eq-refl t = {!!}

-- eq-sym : ∀ (t u : Γ ⊢ a) → Φ ⊩ eq t u → _ -- Φ ⊩ eq u t 
-- eq-sym t u r = R (eq v0 (u p)) r {!!}

-- eq-trans : ∀ (t u w : Γ ⊢ a) →
--          Φ ⊩ eq t u → Φ ⊩ eq u w → _ -- Φ ⊩ eq ϕ φ
-- eq-trans t u w r q = R (eq (u p) v0) q {!!}
