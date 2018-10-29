------------------------------------------------------------------------
-- A universe-polymorphic unit type in Agda

module CCC.Examples.Unit where

import Function.Equality as SetoidFun
open import Relation.Binary hiding (_⇒_)

-- We're defining our own unit type here since the one in Data.Unit is
-- not universe-polymorphic.
record ⊤ {a} : Set a where
  instance constructor tt

-- The unit type forms a terminal setoid with the trivial relation.

⊤-setoid : ∀ {a b} → Setoid a b
⊤-setoid = record
  { Carrier       = ⊤
  ; _≈_           = λ _ _ → ⊤
  ; isEquivalence = record
    { refl  = tt
    ; sym   = λ _   → tt
    ; trans = λ _ _ → tt
    }
  }

-- The unique map into the terminal setoid
⊤-intro : ∀ {c r} → (s : Setoid c r) → s SetoidFun.⟶ ⊤-setoid {c} {r}
⊤-intro s = record
  { _⟨$⟩_ = λ _ → tt
  ; cong  = λ _ → tt
  }
