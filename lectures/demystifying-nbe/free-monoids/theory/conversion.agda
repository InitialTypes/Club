-- Equational theory, conversion
module free-monoids.theory.conversion
  (X : Set)
  where

open import Relation.Binary
  using (Setoid)

open Setoid
  using    (Carrier)
  renaming (refl to ≋-refl; sym to ≋-sym; trans to ≋-trans)

import Relation.Binary.Construct.Closure.Equivalence as EqClosure

open import Relation.Binary.PropositionalEquality
  using    (_≡_)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂; subst to ≡-subst; isEquivalence to ≡-equiv)

open import free-monoids.theory.signature X
open import free-monoids.theory.reduction X

infix 19 _∼_
infix  3 ⊢∼∶-syntax

_∼_ : (t u : Tm Γ a) → Set -- \~
_∼_ = EqClosure.EqClosure _⟶_

⊢∼∶-syntax = λ Γ a t t' → _∼_ {Γ} {a} t t' -- \vdash \--> \~ \:
syntax ⊢∼∶-syntax Γ a t t' = Γ ⊢ t ∼ t' ∶ a

Tm-setoid : (Γ : Ctx) → (a : Ty) → Setoid _ _
Tm-setoid Γ a = EqClosure.setoid (_⟶_ {Γ} {a})

module _ {Γ : Ctx} {a : Ty} where
  open Setoid (Tm-setoid Γ a) using () renaming (refl to ∼-refl; reflexive to ∼-reflexive; sym to ∼-sym; trans to ∼-trans) public

  ∼-reflexive˘ : {t t' : Tm Γ a} → (t'≡t : t' ≡ t) → t ∼ t'
  ∼-reflexive˘ t'≡t = ∼-reflexive (≡-sym t'≡t)

module _ where
  unit-left∼ :
                   (t : Γ ⊢ ∗) →
                   ---------------------------------
                   Γ ⊢ e • t ∼ t ∶ ∗

  unit-right∼ :
                   (t : Γ ⊢ ∗) →
                   ---------------------------------
                   Γ ⊢ t • e ∼ t ∶ ∗

  assoc-right∼ :
                   (t u v : Γ ⊢ ∗) →
                   ---------------------------------
                   Γ ⊢ (t • u) • v ∼ t • (u • v) ∶ ∗

  ∼-cong-•-left :
                   (u    : Γ ⊢ ∗)          →
                   (t∼t' : Γ ⊢ t ∼ t' ∶ ∗) →
                   ---------------------------------
                   Γ ⊢ t • u ∼ t' • u ∶ ∗

  ∼-cong-•-right :
                   (t    : Γ ⊢ ∗)          →
                   (u∼u' : Γ ⊢ u ∼ u' ∶ ∗) →
                   ---------------------------------
                   Γ ⊢ t • u ∼ t • u' ∶ ∗

  ∼-cong-• :
                   (t∼t' : Γ ⊢ t ∼ t' ∶ ∗) →
                   (u∼u' : Γ ⊢ u ∼ u' ∶ ∗) →
                   ---------------------------------
                   Γ ⊢ t • u ∼ t' • u' ∶ ∗

  unit-left∼ t                         = EqClosure.return (unit-left t)
  unit-right∼ t                        = EqClosure.return (unit-right t)
  assoc-right∼ t u v                   = EqClosure.return (assoc-right t u v)
  ∼-cong-•-left u                      = EqClosure.gmap (_• u) (cong-left u)
  ∼-cong-•-right t                     = EqClosure.gmap (t •_) (cong-right t)
  ∼-cong-• {t' = t'} {u = u} t∼t' u∼u' = ∼-trans (∼-cong-•-left u t∼t') (∼-cong-•-right t' u∼u')
