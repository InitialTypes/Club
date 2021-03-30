module Farmer where

open import Data.List.Membership.Propositional

open import STLC

infix 8 _⊩_

data _⊩_ (Φ : FormCtx Γ) : Form Γ → Set where
  Ass : t ∈ Φ → Φ ⊩ t

  R : (ψ : Form (Γ `, a)) → Φ ⊩ eq t u → Φ ⊩ ψ [ t ]
    --------------------------------------------------
    →                  Φ ⊩ ψ [ u ]

  A1 : Φ ⊩ `∀ ⋆ ⇒ ⋆ ﹒ app v0 T ∧ app v0 F ⇔ `∀ ⋆ ﹒ app v1 v0

  A2 : Φ ⊩ `∀ a ﹒ `∀ a ﹒ eq v1 v0 `⇒ `∀ a ⇒ ⋆ ﹒ app v0 v2 ⇔ app v0 v1

  A3 : Φ ⊩ `∀ a ⇒ b ﹒ `∀ a ⇒ b ﹒ eq v1 v0 ⇔ `∀ a ﹒ eq (app v2 v0) (app v1 v0)

  A4 : {t : Γ `, a ⊢ b} {u : Γ ⊢ a} → Φ ⊩ eq (app (lam t) u) (t [ u ]) 

T-true : Φ ⊩ T
T-true = R (eq v0 (lam[ ⋆ ] v0))
           (A4 {t = v0} {u = lam[ ⋆ ] v0})
           {!A4!}

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
