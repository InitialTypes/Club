{-# OPTIONS --rewriting #-}
module Farmer where

open import Agda.Builtin.Equality.Rewrite

open import Data.List.Membership.Propositional
open import Level
open import Relation.Binary.PropositionalEquality hiding ([_]; isEquivalence)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.Reasoning.MultiSetoid

open import STLC

open Setoid hiding (reflexive)
open IsEquivalence hiding (reflexive) renaming (refl to reflexive; sym to symmetry; trans to transitivity)

{-# REWRITE sub-refl sub-trans sub-wk #-}

infix 8 _⊢_

data _⊢_ (Φ : FormCtx Γ) : Form Γ → Set where
  Ass : t ∈ Φ → Φ ⊢ t

  R : (ψ : Form (Γ `, a))
    → Φ ⊢ t `= u → Φ ⊢ ψ [ t /0]
    ----------------------------
    →        Φ ⊢ ψ [ u /0]

  A1 : Φ ⊢ `∀ ⋆ ⇒ ⋆ ﹒ v0 · `⊤ `∧ v0 · `⊥ `⇔ `∀ ⋆ ﹒ v1 · v0

  A2 : Φ ⊢ `∀ a ﹒ `∀ a ﹒ v1 `= v0 `⇒ `∀ a ⇒ ⋆ ﹒ v0 · v2 `⇔ v0 · v1

  A3 : Φ ⊢ `∀ a ⇒ b ﹒ `∀ a ⇒ b ﹒ v1 `= v0 `⇔ `∀ a ﹒ v2 · v0 `= v1 · v0

  A4 : Φ ⊢ (`λ t) · u `= t [ u /0]

  A5 : Φ ⊢ `∃! t `⇒ t [ iota t /0]

  A6 : Φ ⊢ `¬ `∃! t `⇒ iota t `= undefined

-- 1. observe that from any equality t `= u we get the equality u `= u by R
-- 2. we want t `= t and have (`λ v0) t `= t
-- 3. thus we get t `= t from (`λ v0) t `= t by R
eq-refl : Φ ⊢ t `= t
eq-refl {t = t} = R {t = (`λ v0) · t} {u = t} (v0 `= t 𝕡) (A4 {t = v0} {u = t}) (A4 {t = v0} {u = t})

eq-trans : Φ ⊢ t `= u → Φ ⊢ u `= v → Φ ⊢ t `= v
eq-trans {t = t} p q = R (t 𝕡 `= v0) q p

eq-sym : Φ ⊢ t `= u → Φ ⊢ u `= t
eq-sym {t = t} p = R (v0 `= t 𝕡) p eq-refl

`=-setoid : (a : Ty) → (Φ : FormCtx Γ) → Setoid 0ℓ 0ℓ
`=-setoid a Φ .Carrier                     = Tm _ a
`=-setoid a Φ ._≈_                         = λ t u → Φ ⊢ t `= u
`=-setoid a Φ .isEquivalence .reflexive    = eq-refl
`=-setoid a Φ .isEquivalence .symmetry     = eq-sym
`=-setoid a Φ .isEquivalence .transitivity = eq-trans

`⇔-setoid : (Φ : FormCtx Γ) → Setoid 0ℓ 0ℓ
`⇔-setoid = `=-setoid Ω

eq-cong : (v : Tm (Γ `, a) b) → Φ ⊢ t `= u → Φ ⊢ v [ t /0] `= v [ u /0]
eq-cong {t = t} v p = R (v [ t /0] 𝕡 `= v) p eq-refl

`⊤-true : Φ ⊢ `⊤
`⊤-true = eq-refl

truth-lemma˘ : Φ ⊢ `⊤ `= φ → Φ ⊢ φ
truth-lemma˘ p = R v0 p `⊤-true

truth-lemma : Φ ⊢ φ `= `⊤ → Φ ⊢ φ
truth-lemma p = truth-lemma˘ (eq-sym p)

-- inverse-truth-lemma : Φ ⊢ φ → Φ ⊢ φ `= `⊤
-- inverse-truth-lemma p = {!!}

-- deduction-theorem : Φ `, φ ⊢ ψ → Φ ⊢ φ `⇒ ψ
-- deduction-theorem = ?

`⊥E : Φ ⊢ `⊥ → Φ ⊢ φ
`⊥E {_} {Φ} {φ} p = truth-lemma h
  where
    h : Φ ⊢ φ `= `⊤
    h = begin⟨ `=-setoid Ω Φ ⟩
        φ
      ≈˘⟨ A4 ⟩
        (`λ v0) · φ
      ≈˘⟨ eq-cong (v0 · φ 𝕡) p ⟩
        (`λ `⊤) · φ
      ≈⟨ A4 ⟩
        `⊤ ∎

`¬E : Φ ⊢ `¬ φ → Φ ⊢ φ → Φ ⊢ ψ
`¬E p q = `⊥E (R v0 p q)

`⊤`=`⊥E : Φ ⊢ `⊤ `= `⊥ → Φ ⊢ φ
`⊤`=`⊥E p = `⊥E (truth-lemma˘ p)

`⊥`=`⊤E : Φ ⊢ `⊥ `= `⊤ → Φ ⊢ φ
`⊥`=`⊤E p = `⊥E (truth-lemma p)

-- `∧I : Φ ⊢ φ → Φ ⊢ ψ → Φ ⊢ φ `∧ ψ
-- `∧I {_} {Φ} {φ} {ψ} p q = {!!}

`∧E₁ : Φ ⊢ φ `∧ ψ → Φ ⊢ φ
`∧E₁ {_} {Φ} {φ} {ψ} p = truth-lemma h
  where
    h : Φ ⊢ φ `= `⊤
    h = begin⟨ `=-setoid Ω Φ ⟩
        φ
      ≈˘⟨ A4 ⟩
        (`λ φ 𝕡) · ψ
      ≈˘⟨ eq-cong (v0 · ψ 𝕡) A4 ⟩
        (`λ `λ v1) · φ · ψ
      ≈˘⟨ A4 ⟩
        (`λ v0 · φ 𝕡 · ψ 𝕡) · (`λ `λ v1)
      ≈˘⟨ eq-cong (v0 · (`λ `λ v1)) p ⟩
        (`λ v0 · `⊤ · `⊤) · (`λ `λ v1)
      ≈⟨ A4 ⟩
        (`λ `λ v1) · `⊤ · `⊤
      ≈⟨ eq-cong (v0 · `⊤) A4 ⟩
        (`λ `⊤) · `⊤
      ≈⟨ A4 ⟩
        `⊤ ∎

`∧E₂ : Φ ⊢ φ `∧ ψ → Φ ⊢ ψ
`∧E₂ {_} {Φ} {φ} {ψ} p = truth-lemma h
  where
    h : Φ ⊢ ψ `= `⊤
    h = begin⟨ `=-setoid Ω Φ ⟩
        ψ
      ≈˘⟨ A4 ⟩
        (`λ v0) · ψ
      ≈˘⟨ eq-cong (v0 · ψ 𝕡) A4 ⟩
        (`λ `λ v0) · φ · ψ
      ≈˘⟨ A4 ⟩
        (`λ v0 · φ 𝕡 · ψ 𝕡) · (`λ `λ v0)
      ≈˘⟨ eq-cong (v0 · (`λ `λ v0)) p ⟩
        (`λ v0 · `⊤ · `⊤) · (`λ `λ v0)
      ≈⟨ A4 ⟩
        (`λ `λ v0) · `⊤ · `⊤
      ≈⟨ eq-cong (v0 · `⊤) A4 ⟩
        (`λ v0) · `⊤
      ≈⟨ A4 ⟩
        `⊤ ∎

-- `∨E : Φ ⊢ φ `∨ ψ → Φ ⊢ χ
-- `∨E = {!!}

-- `∨I₁ : Φ ⊢ φ → Φ ⊢ φ `∨ ψ
-- `∨I₁ p = {!!}

-- `⇒E : Φ ⊢ φ `⇒ ψ → Φ ⊢ φ → Φ ⊢ ψ
-- `⇒E p q = {!!}

-- MP = `⇒E

`∀E : Φ ⊢ `∀ ψ → Φ ⊢ ψ [ t /0]
`∀E {Φ = Φ} {ψ = ψ} {t = t} p = truth-lemma h
  where
    h : Φ ⊢ ψ [ t /0] `= `⊤
    h = begin⟨ `=-setoid Ω Φ ⟩
        ψ [ t /0]
      ≈˘⟨ A4 ⟩
        (`λ ψ) · t
      ≈⟨ eq-cong (v0 · t 𝕡) p ⟩
        (`λ `⊤) · t
      ≈⟨ A4 ⟩
        `⊤ ∎

-- LEM : Φ ⊢ φ ∨ ¬ φ
-- LEM = {!!}

-- I : Φ ⊢ φ `⇒ φ
-- I = {!!}
