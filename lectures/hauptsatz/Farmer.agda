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

  A5 : Φ ⊩ `∃! t `⇒ t [ iota t ]

  A6 : Φ ⊩ ¬ `∃! t `⇒ iota t `= ⊥

eq-refl : Φ ⊩ t `= t
eq-refl = {!R {ψ = v0 `= t p} (A4 {t = v0} {u = t}) A4!}

T-true : Φ ⊩ T
T-true = eq-refl

truth-lemma : Φ ⊩ T `= ψ → Φ ⊩ ψ
truth-lemma p = R p T-true

-- `∀E :  Φ ⊩ `∀ ψ → Φ ⊩ ψ [ t ]
-- `∀E p = {!!}

-- ∧E₁ :  Φ ⊩ φ ∧ ψ → Φ ⊩ φ
-- ∧E₁ p = {!!}

-- LEM : Φ ⊩ φ ∨ ¬ φ
-- LEM = {!!}

-- I : Φ ⊩ φ `⇒ φ
-- I = {!!}

eq-sym : Φ ⊩ t `= u → Φ ⊩ u `= t
eq-sym {u = u} p = {!R {ψ = v0 `= u 𝕡} p eq-refl!}

eq-trans : Φ ⊩ t `= u → Φ ⊩ u `= v → Φ ⊩ t `= v
eq-trans {t = t} p q = {!R {ψ = t 𝕡 `= v0} q p!}
