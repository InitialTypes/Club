module free-monoids.theory.reduction
  (X : Set)
  where

open import Relation.Binary
  using (Preorder)

open Preorder
  using    (Carrier)
  renaming (refl to ≤-refl; trans to ≤-trans) -- \leq

import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties as StarProperties

open import Relation.Binary.PropositionalEquality
  using    (_≡_)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂; subst to ≡-subst; isEquivalence to ≡-equiv)

open import free-monoids.theory.signature X

infix 19 _⟶_ _⟶⋆_
infix  3 ⊢⟶∶-syntax ⊢⟶⋆∶-syntax

data _⟶_ : {Γ : Ctx} → {a : Ty} → (t t' : Tm Γ a) → Set -- \-->

⊢⟶∶-syntax = λ Γ a t t' → _⟶_ {Γ} {a} t t' -- \vdash \--> \:
syntax ⊢⟶∶-syntax Γ a t t' = Γ ⊢ t ⟶ t' ∶ a

data _⟶_ where
  unit-left :
                (t : Γ ⊢ ∗) →
                ---------------------------------
                Γ ⊢ e • t ⟶ t ∶ ∗

  unit-right :
                (t : Γ ⊢ ∗) →
                ---------------------------------
                Γ ⊢ t • e ⟶ t ∶ ∗

  assoc-right :
                (t u v : Γ ⊢ ∗) →
                ---------------------------------
                Γ ⊢ (t • u) • v ⟶ t • (u • v) ∶ ∗

  cong-left :
                (u    : Γ ⊢ ∗) →
                (t⟶t' : Γ ⊢ t ⟶ t' ∶ ∗) →
                ---------------------------------
                Γ ⊢ t • u ⟶ t' • u ∶ ∗

  cong-right :
                (t    : Γ ⊢ ∗) →
                (u⟶u' : Γ ⊢ u ⟶ u' ∶ ∗) →
                ---------------------------------
                Γ ⊢ t • u ⟶ t • u' ∶ ∗

_⟶⋆_ : (t t' : Tm Γ a) → Set -- \--> \star
_⟶⋆_ = Star.Star _⟶_

⊢⟶⋆∶-syntax = λ Γ a t t' → _⟶⋆_ {Γ} {a} t t' -- \vdash \--> \star \:
syntax ⊢⟶⋆∶-syntax Γ a t t' = Γ ⊢ t ⟶⋆ t' ∶ a

Tm-preorder : (Γ : Ctx) → (a : Ty) → Preorder _ _ _
Tm-preorder Γ a = StarProperties.preorder (_⟶_ {Γ} {a})

module _ {Γ : Ctx} {a : Ty} where
  open Preorder (Tm-preorder Γ a) using () renaming (refl to ⟶⋆-refl; reflexive to ⟶⋆-reflexive; trans to ⟶⋆-trans) public
  open StarProperties             using () renaming (◅◅-assoc to ∙⋆-assoc)                                          public

  infixr 20 _∙⋆_

  ⟶⋆-reflexive˘ : {t t' : Tm Γ a} → (t'≡t : t' ≡ t) → t ⟶⋆ t'
  ⟶⋆-reflexive˘ t'≡t = ⟶⋆-reflexive (≡-sym t'≡t)

  id⋆  = λ t → ⟶⋆-refl {t}

  _∙⋆_ = ⟶⋆-trans

module _ where
  open Star using (return; gmap)

  unit-left⋆ :
                    (t : Γ ⊢ ∗) →
                    ----------------------------------
                    Γ ⊢ e • t ⟶⋆ t ∶ ∗

  unit-right⋆ :
                    (t : Γ ⊢ ∗) →
                    ----------------------------------
                    Γ ⊢ t • e ⟶⋆ t ∶ ∗

  assoc-right⋆ :
                    (t u v : Γ ⊢ ∗) →
                    ----------------------------------
                    Γ ⊢ (t • u) • v ⟶⋆ t • (u • v) ∶ ∗

  ⟶⋆-cong-•-left :
                    (u     : Γ ⊢ ∗)          →
                    (t⟶⋆t' : Γ ⊢ t ⟶⋆ t' ∶ ∗) →
                    ----------------------------------
                    Γ ⊢ t • u ⟶⋆ t' • u ∶ ∗

  ⟶⋆-cong-•-right :
                    (t     : Γ ⊢ ∗)          →
                    (u⟶⋆u' : Γ ⊢ u ⟶⋆ u' ∶ ∗) →
                    ----------------------------------
                    Γ ⊢ t • u ⟶⋆ t • u' ∶ ∗

  ⟶⋆-cong-• :
                    (t⟶⋆t' : Γ ⊢ t ⟶⋆ t' ∶ ∗) →
                    (u⟶⋆u' : Γ ⊢ u ⟶⋆ u' ∶ ∗) →
                    ----------------------------------
                    Γ ⊢ t • u ⟶⋆ t' • u' ∶ ∗

  unit-left⋆ t                            = return (unit-left t)
  unit-right⋆ t                           = return (unit-right t)
  assoc-right⋆ t u v                      = return (assoc-right t u v)
  ⟶⋆-cong-•-left u                        = gmap (_• u) (cong-left u)
  ⟶⋆-cong-•-right t                       = gmap (t •_) (cong-right t)
  ⟶⋆-cong-• {t' = t'} {u = u} t⟶⋆t' u⟶⋆u' = ⟶⋆-trans (⟶⋆-cong-•-left u t⟶⋆t') (⟶⋆-cong-•-right t' u⟶⋆u')
