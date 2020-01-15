{-# OPTIONS --postfix-projections #-} -- To work interactively with copatterns

module CCCInternalLanguage where

-- Setoid equality reasoning.

open import Relation.Binary using (Setoid; IsEquivalence); open Setoid; open IsEquivalence
import Relation.Binary.Reasoning.MultiSetoid as SetoidR

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

  eq-comp : ∀{a b c} {f f' : Hom b c} {g g' : Hom a b}
    → f ~ f'
    → g ~ g'
    → f ∘ g ~ f' ∘ g'

  eq-pair : ∀{a b c} {f f' : Hom a b} {g g' : Hom a c}
    → f ~ f'
    → g ~ g'
    → pair f g ~ pair f' g'

  eq-curry : ∀{a b c} {f f' : Hom (c * a) b}
    → f ~ f'
    → curry f ~ curry f'

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

open SetoidR

-- A more general η-law.

curry-apply' : ∀{a b c} (f : Hom c (a ⇒ b))
  → curry (apply ∘ lift f) ~ f

curry-apply' f = begin⟨ homSetoid _ _ ⟩
  curry (apply ∘ lift f)   ≈⟨ eq-sym curry-comp ⟩
  curry apply ∘ f          ≈⟨ eq-comp curry-apply eq-refl ⟩
  id ∘ f                   ≈⟨ id-l ⟩
  f
  ∎

-- Contraction of lifting and pairing.

lift-pair : ∀ {a b c} (f : Hom c b) (g : Hom c a)
  → lift f ∘ pair id g ~ pair f g
lift-pair f g = begin⟨ homSetoid _ _ ⟩
    lift f ∘ pair id g
  ≈⟨ pair-comp ⟩
    pair (f ∘ fst ∘ pair id g) (snd ∘ pair id g)
  ≈⟨ eq-pair
       (begin⟨ homSetoid _ _ ⟩
         f ∘ fst ∘ pair id g     ≈⟨ assoc ⟩
         f ∘ (fst ∘ pair id g)   ≈⟨ eq-comp eq-refl fst-pair ⟩
         f ∘ id                  ≈⟨ id-r ⟩
         f                       ∎)
       snd-pair ⟩
    pair f g
  ∎

-- A more familiar β-law.

beta : ∀ {a b c} (f : Hom (c * a) b) (g : Hom c a)
  → apply ∘ pair (curry f) g ~ f ∘ pair id g
beta f g = begin⟨ homSetoid _ _ ⟩
    apply ∘ pair (curry f) g
  ≈⟨ eq-comp eq-refl (eq-sym (lift-pair (curry f) g)) ⟩
    apply ∘ (lift (curry f) ∘ pair id g)
  ≈⟨ eq-sym assoc ⟩
    apply ∘ lift (curry f) ∘ pair id g
  ≈⟨ eq-comp apply-curry eq-refl ⟩
    f ∘ pair id g
  ∎

-- Uniqueness properties for the various mediating morphisms.

pair-unique : ∀ {a b c} (f : Hom c a) (g : Hom c b) (h : Hom c (a * b)) →
              fst ∘ h ~ f → snd ∘ h ~ g → h ~ pair f g
pair-unique f g h hyp₁ hyp₂ = begin⟨ homSetoid _ _ ⟩
  h                          ≈⟨ eq-sym (id-l) ⟩
  id ∘ h                     ≈⟨ eq-comp id-pair eq-refl ⟩
  pair fst snd ∘ h           ≈⟨ pair-comp ⟩
  pair (fst ∘ h) (snd ∘ h)   ≈⟨ eq-pair hyp₁ hyp₂ ⟩
  pair f g                   ∎

curry-unique : ∀ {a b c} (f : Hom (c * a) b) (h : Hom c (a ⇒ b)) →
               apply ∘ lift h ~ f → h ~ curry f
curry-unique f h hyp = begin⟨ homSetoid _ _ ⟩
  h                      ≈⟨ eq-sym id-l ⟩
  id ∘ h                 ≈⟨ eq-comp (eq-sym curry-apply) eq-refl ⟩
  curry apply ∘ h        ≈⟨ curry-comp ⟩
  curry (apply ∘ lift h) ≈⟨ eq-curry hyp ⟩
  curry f                ∎
