{-# OPTIONS --postfix-projections #-} -- To work interactively with copatterns

module CCCInternalLanguage where

-- Setoid equality reasoning.

open import Relation.Binary using (Setoid; IsEquivalence); open Setoid; open IsEquivalence
import Relation.Binary.EqReasoning as EqR

-- We use types as objects.

open import Types

-- Morphism of the free CCC (but lacking arbitrary morphisms)

infixl 4 _∘_

data Hom : (a b : Ty) → Set where
  -- Category
  id    : ∀ {a} → Hom a a
  _∘_   : ∀ {a b c} → Hom b c → Hom a b → Hom a c  -- \ o

  -- Product
  fst   : ∀ {a b} → Hom (a * b) a
  snd   : ∀ {a b} → Hom (a * b) b
  pair  : ∀ {c a b} → Hom c a → Hom c b → Hom c (a * b)

  -- Terminal
  unit  : ∀ {a} → Hom a 𝟙

  -- Exponential
  curry : ∀ {a b c} → Hom (c * a) b → Hom c (a ⇒ b)
  apply : ∀ {a b} → Hom ((a ⇒ b) * a) b

-- Defined morphism

_⊗_ : ∀{a b c d} → Hom a b → Hom c d → Hom (a * c) (b * d)  -- \ o x
f ⊗ g = pair (f ∘ fst) (g ∘ snd)

-- lift f = f ⊗ id
lift : ∀{c a b} → Hom a b → Hom (a * c) (b * c)
lift f = pair (f ∘ fst) snd

uncurry : ∀ {a b c} → Hom c (a ⇒ b) → Hom (c * a) b
uncurry f = apply ∘ lift f

-- Equalities

infix 0 _~_

data _~_ : ∀ {a b} (f g : Hom a b) → Set where

  -- Category laws:

  id-l : ∀{a b} {f : Hom a b}
    → id ∘ f ~ f

  id-r : ∀{a b} {f : Hom a b}
    → f ∘ id ~ f

  assoc : ∀{a b c d} {f : Hom c d} {g : Hom b c} {h : Hom a b}
    → (f ∘ g) ∘ h ~ f ∘ (g ∘ h)

  -- Product laws:

  -- The β laws.

  fst-pair : ∀{a b c} {f : Hom c a} {g : Hom c b}
    → fst ∘ pair f g ~ f

  snd-pair : ∀{a b c} {f : Hom c a} {g : Hom c b}
    → snd ∘ pair f g ~ g

  -- The η law.

  id-pair : ∀{a b}
    → id {a * b} ~ pair fst snd

  -- The naturality law.

  pair-comp : ∀{a b c d} {h : Hom d c} {f : Hom c a} {g : Hom c b}
    → pair f g ∘ h ~ pair (f ∘ h) (g ∘ h)

  -- Law for the terminal object:  The η law.

  unit : ∀{a} {f : Hom a 𝟙}
    → f ~ unit

  -- Laws for the exponential:

  -- The β law.

  apply-curry : ∀{a b c} {f : Hom (c * a) b}
    → apply ∘ lift (curry f) ~ f

  -- The η law.

  curry-apply : ∀{a b}
    → curry apply ~ id {a ⇒ b}

  -- The naturality law.

  curry-comp : ∀{a b c d} {h : Hom d c} {f : Hom (c * a) b}
    → curry f ∘ h ~ curry (f ∘ lift h)

  -- Congruence laws:

  eq-cong : ∀{a b c} {f f' : Hom b c} {g g' : Hom a b}
    → f ~ f'
    → g ~ g'
    → f ∘ g ~ f' ∘ g'

  -- Equivalence laws:

  eq-refl : ∀{a b} {f : Hom a b}
    → f ~ f

  eq-sym : ∀{a b} {f g : Hom a b}
    → g ~ f
    → f ~ g

  eq-trans : ∀{a b} {f g h : Hom a b}
    → f ~ g
    → g ~ h
    → f ~ h

-- Each Homset is a setoid.

homSetoid : (a b : Ty) → Setoid _ _
homSetoid a b .Carrier = Hom a b
homSetoid a b ._≈_     = _~_
homSetoid a b .isEquivalence .refl  = eq-refl
homSetoid a b .isEquivalence .sym   = eq-sym
homSetoid a b .isEquivalence .trans = eq-trans

-- Derived laws.

-- A more general η-law.

curry-apply' : ∀{a b c} (f : Hom c (a ⇒ b))
  → curry (apply ∘ lift f) ~ f

curry-apply' f = begin
  curry (apply ∘ lift f)   ≈⟨ eq-sym curry-comp ⟩
  curry apply ∘ f          ≈⟨ eq-cong curry-apply eq-refl ⟩
  id ∘ f                   ≈⟨ id-l ⟩
  f
  ∎ where open EqR (homSetoid _ _)
