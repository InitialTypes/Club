module CCC.Examples.Setoid where

open import Agda.Primitive  -- Universe levels
open import Data.Product as Prod using (_,_; proj₁; proj₂; _×_; <_,_>)
import Function.Equality as SetoidFun
open import Relation.Binary hiding (_⇒_)

open import CCC
open import CCC.Examples.Unit
open import CCC.Examples.Relation

------------------------------------------------------------------------
-- Cartesian products over setoids

module SetoidProd where

  open Setoid
  open SetoidFun
  open Π

  -- The cartesian product of two setoids.

  _×'_ : ∀ {a₁ a₂ b₁ b₂} →
         Setoid a₁ a₂ → Setoid b₁ b₂ → Setoid (a₁ ⊔ b₁) (a₂ ⊔ b₂)
  A ×' B = record
    { Carrier       = Carrier A × Carrier B
    ; _≈_           = _≈_ A ⊗ _≈_ B
    ; isEquivalence = ⊗-isEquivalence (isEquivalence A) (isEquivalence B)
    }

  -- Projection and pairing maps

  π₁ : ∀ {a₁ a₂ b₁ b₂} {A : Setoid a₁ a₂} {B : Setoid b₁ b₂} → A ×' B ⟶ A
  π₁ = record { _⟨$⟩_ = proj₁ ; cong = proj₁ }

  π₂ : ∀ {a₁ a₂ b₁ b₂} {A : Setoid a₁ a₂} {B : Setoid b₁ b₂} → A ×' B ⟶ B
  π₂ = record { _⟨$⟩_ = proj₂ ; cong = proj₂ }

  <_,_>' : ∀ {a₁ a₂ b₁ b₂ c₁ c₂} {A : Setoid a₁ a₂} {B : Setoid b₁ b₂}
           {C : Setoid c₁ c₂} → (A ⟶ B) → (A ⟶ C) → A ⟶ B ×' C
  < f , g >' = record
    { _⟨$⟩_ = < f ⟨$⟩_ , g ⟨$⟩_ >
    ; cong  = < cong f , cong g >
    }

  -- Currying and uncurrying maps

  curry' : ∀ {a₁ a₂ b₁ b₂ c₁ c₂} {A : Setoid a₁ a₂} {B : Setoid b₁ b₂}
           {C : Setoid c₁ c₂} → (A ×' B ⟶ C) → (A ⟶ B ⇨ C)
  curry' {A = A} f = record
    { _⟨$⟩_ = λ x → record
      { _⟨$⟩_ = λ y     → f ⟨$⟩ (x , y)
      ; cong  = λ y₁≈y₂ → (cong f) (refl A , y₁≈y₂)
      }
    ; cong  = λ x₁≈x₂ y₁≈y₂ → (cong f) (x₁≈x₂ , y₁≈y₂)
    }


------------------------------------------------------------------------
-- (Small) setoids and equality-preserving functions form a CCC

Setoid-CCC : ∀ {a} → CCC (lsuc a) _ _
Setoid-CCC {a} = record

  { cc = record
      -- Objects and morphisms.
      { Ob   = Setoid a a
      ; Homs = _⇨_

      -- Category operations
      ; id   = λ _ → id
      ; comp = _∘_

      -- Category laws
      ; id-l  = λ f → cong f
      ; id-r  = λ f → cong f
      ; assoc = λ f g h → cong (f ∘ g ∘ h)

      ; comp-cong = λ f≈₂₃f' g≈₁₂g' x≈₁y → f≈₂₃f' (g≈₁₂g' x≈₁y)

      -- Product object and projections
      ; Prod = _×'_
      ; π₁   = π₁
      ; π₂   = π₂

      -- Pairing and β-laws
      ; pair = <_,_>'
      ; β-π₁ = λ {a b c f g} → cong f
      ; β-π₂ = λ {a b c f g} → cong g

      -- Uniqueness of pairing
      ; pair-unique = λ f g h eq₁ eq₂ → < eq₁ , eq₂ >

      -- Terminal object
      ; Unit = ⊤-setoid
      ; unit = ⊤-intro

      -- Uniqueness of terminal morphism
      ; unit-unique = λ h _ → tt
      }

  -- Exponential object and application
  ; Arr   = _⇨_
  ; apply = record
    { _⟨$⟩_ = λ{ (f , x)     → f ⟨$⟩ x }
    ; cong  = λ{ (f≈g , x≈y) → f≈g x≈y }
    }

  -- Currying and the computation law for application
  ; curry        = curry'
  ; β-apply      = λ f → cong f

  -- Uniqueness of curry
  ; curry-unique = λ f h eq x₁≈x₂ y₁≈y₂ → eq (x₁≈x₂ , y₁≈y₂)
  }
  where
    open SetoidFun
    open Π
    open SetoidProd
