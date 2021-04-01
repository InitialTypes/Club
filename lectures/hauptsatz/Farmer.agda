{-# OPTIONS --rewriting #-}
module Farmer where

open import Agda.Builtin.Equality.Rewrite

open import Data.List.Membership.Propositional
open import Relation.Binary.PropositionalEquality hiding ([_])

open import STLC

{-# REWRITE sub-refl sub-trans #-}

infix 8 _⊩_

data _⊩_ (Φ : FormCtx Γ) : Form Γ → Set where
  Ass : t ∈ Φ → Φ ⊩ t

  R : (ψ : Form (Γ `, a))
    → Φ ⊩ t `= u → Φ ⊩ ψ [ t /0]
    ----------------------------
    →        Φ ⊩ ψ [ u /0]

  A1 : Φ ⊩ `∀ ⋆ ⇒ ⋆ ﹒ v0 · `⊤ `∧ v0 · `⊥ `⇔ `∀ ⋆ ﹒ v1 · v0

  A2 : Φ ⊩ `∀ a ﹒ `∀ a ﹒ v1 `= v0 `⇒ `∀ a ⇒ ⋆ ﹒ v0 · v2 `⇔ v0 · v1

  A3 : Φ ⊩ `∀ a ⇒ b ﹒ `∀ a ⇒ b ﹒ v1 `= v0 `⇔ `∀ a ﹒ v2 · v0 `= v1 · v0

  A4 : Φ ⊩ (`λ t) · u `= t [ u /0]

  A5 : Φ ⊩ `∃! t `⇒ t [ iota t /0]

  A6 : Φ ⊩ `¬ `∃! t `⇒ iota t `= undefined

-- 1. observe that from any equality t `= u we get the equality u `= u by R
-- 2. we want t `= t and have (`λ v0) t `= t
-- 3. thus we get t `= t from (`λ v0) t `= t by R
eq-refl : Φ ⊩ t `= t
eq-refl {t = t} = R {t = (`λ v0) · t} {u = t} (v0 `= t 𝕡) (A4 {t = v0} {u = t}) (A4 {t = v0} {u = t})

`⊤-true : Φ ⊩ `⊤
`⊤-true = eq-refl

truth-lemma : Φ ⊩ `⊤ `= ψ → Φ ⊩ ψ
truth-lemma p = R v0 p `⊤-true

-- `∀E :  Φ ⊩ `∀ ψ → Φ ⊩ ψ [ t ]
-- `∀E p = {!!}

-- ∧E₁ :  Φ ⊩ φ ∧ ψ → Φ ⊩ φ
-- ∧E₁ p = {!!}

-- LEM : Φ ⊩ φ ∨ ¬ φ
-- LEM = {!!}

-- I : Φ ⊩ φ `⇒ φ
-- I = {!!}

eq-sym : Φ ⊩ t `= u → Φ ⊩ u `= t
eq-sym {t = t} p = R (v0 `= t 𝕡) p eq-refl

eq-trans : Φ ⊩ t `= u → Φ ⊩ u `= v → Φ ⊩ t `= v
eq-trans {t = t} p q = R (t 𝕡 `= v0) q p
