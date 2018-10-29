module CCC.Examples.Relation where

open import Agda.Primitive  -- Universe levels
open import Data.Product as Prod using (_,_; proj₁; proj₂; _×_; <_,_>)
open import Relation.Binary hiding (_⇒_)

-- The tensor product of two binary relations.

_⊗_ : ∀ {c₁ r₁ c₂ r₂} {A : Set c₁} {B : Set c₂} →
      Rel A r₁ → Rel B r₂ → Rel (A × B) (r₁ ⊔ r₂)
(R ⊗ Q) (x₁ , y₁) (x₂ , y₂) = R x₁ x₂ × Q y₁ y₂

-- The tensor product of two equivalences is an equivalence.

⊗-isEquivalence : ∀ {c₁ r₁ c₂ r₂} {A : Set c₁} {B : Set c₂}
                  {P : Rel A r₁} {Q : Rel B r₂} →
                  IsEquivalence P → IsEquivalence Q → IsEquivalence (P ⊗ Q)
⊗-isEquivalence eP eQ = record
  { refl  = EP.refl , EQ.refl
  ; sym   = λ{ (p , q) → EP.sym p , EQ.sym q }
  ; trans = λ{ (p₁ , q₁) (p₂ , q₂) → (EP.trans p₁ p₂) , (EQ.trans q₁ q₂) }
  }
  where
    module EP = IsEquivalence eP
    module EQ = IsEquivalence eQ
