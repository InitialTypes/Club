-- Cartesian closed categories

module CCC where

open import Agda.Primitive  -- Universe levels
open import Relation.Binary using (Setoid; IsEquivalence); open Setoid; open IsEquivalence
import Relation.Binary.Reasoning.Setoid as EqR

open import CC as _ using (CC)

---------------------------------------------------------------------------
-- Cartesian closed category as mathematical structure
---------------------------------------------------------------------------

record CCC o m e : Set (lsuc (o ⊔ m ⊔ e)) where

  ---------------------------------------------------------------------------
  -- Cartesian category
  ---------------------------------------------------------------------------

  field
    cc : CC o m e

  open CC cc public

  ---------------------------------------------------------------------------
  -- Closed
  ---------------------------------------------------------------------------

  field
    -- Exponential object and application
    Arr  : (a b : Ob) → Ob
    eval : ∀{a b} → Hom (Prod (Arr a b) a) b

  IsCurry : ∀{a b c} (f : Hom (Prod c a) b) (h : Hom c (Arr a b)) → Set _
  IsCurry f h = Eq (comp eval (lift h)) f

  field
    curry  : ∀{a b c} (f : Hom (Prod c a) b) → Hom c (Arr a b)
    β-eval : ∀{a b c} (f : Hom (Prod c a) b) → IsCurry f (curry f)

    curry-unique : ∀{a b c} (f : Hom (Prod c a) b) (h : Hom c (Arr a b))
      → IsCurry f h
      → Eq h (curry f)

  ---------------------------------------------------------------------------
  -- Derived laws for exponentials
  ---------------------------------------------------------------------------

  -- Congruence law for currying

  curry-cong : ∀{a b c} {f f' : Hom (Prod c a) b}
    → (e : Eq f f')
    → Eq (curry f) (curry f')
  curry-cong {a} {b} {c} {f} {f'} e = curry-unique f' (curry f) eq
    where
    eq : Eq (comp eval (lift (curry f))) f'
    eq = eq-trans (β-eval f) e

  -- Naturality law for currying

  curry-nat : ∀{a b c d} (f : Hom (Prod c a) b) (h : Hom d c)
    → Eq (comp (curry f) h)
         (curry (comp f (lift h)))
  curry-nat {a} {b} {c} {d} f h =
      curry-unique (comp f (lift h)) (comp (curry f) h) eq
    where
    eq : Eq (comp eval (lift (comp (curry f) h)))
            (comp f (lift h))
    eq = begin
      comp eval (lift (comp (curry f) h))          ≈⟨ comp-cong eq-refl (lift-comp _ _) ⟩
      comp eval (comp (lift (curry f)) (lift h))   ≈⟨ eq-sym (assoc _ _ _) ⟩
      comp (comp eval (lift (curry f))) (lift h)   ≈⟨ comp-cong (β-eval _) eq-refl ⟩
      comp f (lift h) ∎ where open EqR (Homs _ _)


  -- Lemma: id is a currying of the eval morphism

  isCurry-eval-id : ∀ {a b} → IsCurry eval (id (Arr a b))
  isCurry-eval-id {a} {b} = begin
    comp eval (lift (id (Arr a b)))   ≈⟨ comp-cong eq-refl

     (begin′
      lift (id (Arr a b))             ≈⟨ pair-cong (id-l _) eq-refl ⟩′
      pair π₁ π₂                      ≈⟨ pair-π ⟩′
      id _
      ∎′ )⟩

    comp eval (id _)                  ≈⟨ id-r _ ⟩
    eval
    ∎ where
      open EqR (Homs _ _)
      module EqR′ = EqR (Homs _ _)
      open EqR′ using () renaming (begin_ to begin′_; _∎ to _∎′)
      infixr 2 step-≈′
      step-≈′ = EqR′.step-≈
      syntax step-≈′ x y≈z x≈y = x ≈⟨ x≈y ⟩′ y≈z

  -- Thus, curry eval is the identity by uniqueness of currying.

  curry-eval : ∀{a b} → Eq (curry eval) (id (Arr a b))
  curry-eval = eq-sym (curry-unique eval (id _) isCurry-eval-id)
