-- Exercise: 1 × A ≅ A

open import Relation.Binary using (Setoid; IsEquivalence); open Setoid; open IsEquivalence
import Relation.Binary.Reasoning.Setoid as EqR

open import CC as _  -- Import the contents, hide the module itself

module Exercises.TheOneTimesAIsomorphicA {o m e} (C : CC o m e) (let open CC C) where

  -- Show that Prod Unit A ≅ A

  -- to : A × 1 → A (just project)

  to : ∀{a} → Hom (Prod Unit a) a
  to {a} = π₂

  -- from : A → 1 × A (⟨id,!⟩)

  from : ∀{a} → Hom a (Prod Unit a)
  from {a} = pair (unit a) (id a)

  -- to ∘ from = id

  -- to-from : ∀{a} → Eq (comp to from) (id a)

  -- from ∘ to = id

  -- from-to : ∀{a} → Eq (comp from to) (id (Prod Unit a))
