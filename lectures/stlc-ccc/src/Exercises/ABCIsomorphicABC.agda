-- Exercise: (A × B) × C ≅ A × (B × C)

open import Relation.Binary using (Setoid; IsEquivalence); open Setoid; open IsEquivalence
import Relation.Binary.Reasoning.Setoid as EqR

open import CC as _  -- Import the contents, hide the module itself

module Exercises.ABCIsomorphicABC {o m e} (C : CC o m e) (let open CC C) where

  -- Show that Prod (Prod A B) C ≅ Prod A (Prod B C)

  -- ltr : (A × B) × C → A × (B × C)

  ltr : ∀{a b c} → Hom (Prod (Prod a b) c) (Prod a (Prod b c))
  ltr = pair (comp π₁ π₁) (pair (comp π₂ π₁) π₂)

  -- rtl : A × (B × C) → (A × B) × C

  rtl : ∀{a b c} → Hom (Prod a (Prod b c)) (Prod (Prod a b) c)
  rtl = pair (pair π₁ (comp π₁ π₂)) (comp π₂ π₂)

  -- ltr ∘ rtl = id

  -- ltr-rtl : ∀{a b c} → Eq (comp ltr rtl) (id (Prod a (Prod b c)))

  -- rtl ∘ ltr = id

  -- rtl-ltr : ∀{a b c} → Eq (comp rtl ltr) (id (Prod (Prod a b) c))
