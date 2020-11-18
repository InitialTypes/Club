-- Cartesian closed categories (alternative definition)

module CCC2 where

open import Agda.Primitive  -- Universe levels
open import Relation.Binary using (Setoid; IsEquivalence); open Setoid; open IsEquivalence
import Relation.Binary.Reasoning.Setoid as EqR

open import CC as _ using (CC)

---------------------------------------------------------------------------
-- Cartesian closed category as mathematical structure
---------------------------------------------------------------------------

record CCC2 o m e : Set (lsuc (o ⊔ m ⊔ e)) where

  -------------------------------------------------------------------------
  -- Cartesian category
  -------------------------------------------------------------------------

  field
    cc : CC o m e

  open CC cc public

  -------------------------------------------------------------------------
  -- Closed
  -------------------------------------------------------------------------

  field
    -- Exponential object
    Arr        : (a b : Ob) → Ob

    curry      : ∀{c a b} (t : Hom (Prod c a) b) → Hom c (Arr a b)
    curry-comp : ∀{c' c a b} {t : Hom (Prod c a) b} {h : Hom c' c}
      → Eq (comp (curry t) h)
           (curry (comp t (pair (comp h π₁) π₂)))

    apply      : ∀{c a b} (f : Hom c (Arr a b)) (x : Hom c a) → Hom c b
    apply-comp : ∀{c' c a b} {f : Hom c (Arr a b)} {x : Hom c a} {h : Hom c' c}
      → Eq (comp (apply f x) h)
           (apply (comp f h) (comp x h))

    β-apply    : ∀{c a b} (t : Hom (Prod c a) b) (x : Hom c a)
      → Eq (apply (curry t) x)
           (comp t (pair (id c) x))
    η-curry    : ∀{c a b} (f : Hom c (Arr a b))
      → Eq (curry (apply (comp f π₁) π₂))
           f
