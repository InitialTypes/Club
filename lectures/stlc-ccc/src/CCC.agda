{-# OPTIONS --postfix-projections #-} -- To work interactively with copatterns

-- Cartesian closed categories

module CCC where

open import Agda.Primitive  -- Universe levels
open import Relation.Binary using (Setoid; IsEquivalence); open Setoid; open IsEquivalence
import Relation.Binary.EqReasoning as EqR


---------------------------------------------------------------------------
-- Cartesian closed category as mathematical structure
---------------------------------------------------------------------------

record CCC o m e : Set (lsuc (o ⊔ m ⊔ e)) where

  ---------------------------------------------------------------------------
  -- Category
  ---------------------------------------------------------------------------

  field
    -- Objects.  We use propositional equality for objects.
    Ob  : Set o

    -- Morphisms.  The equality may be non-trivial.
    Homs : (a b : Ob) → Setoid m e

  -- Abbreviations to access Hom-set and its equality

  Hom : (a b : Ob) → Set m
  Hom a b = Homs a b .Carrier

  Eq : ∀{a b} (f g : Hom a b) → Set e
  Eq f g = Homs _ _ ._≈_ f g

  eq-refl : ∀{a b} {f : Hom a b} → Eq f f
  eq-refl {a} {b} {f} = Homs a b .isEquivalence .refl {f}

  eq-sym : ∀{a b} {f g : Hom a b} → Eq g f → Eq f g
  eq-sym e = Homs _ _ .isEquivalence .sym e

  eq-trans : ∀{a b} {f g h : Hom a b} → Eq f g → Eq g h → Eq f h
  eq-trans e e' = Homs _ _ .isEquivalence .trans e e'

  field
    -- Category operations
    id   : (a : Ob) → Hom a a
    comp : {a b c : Ob} (f : Hom b c) (g : Hom a b) → Hom a c

    -- Category laws
    id-l : ∀{a b} (f : Hom a b)
      → Eq (comp (id b) f) f
    id-r : ∀{a b} (f : Hom a b)
      → Eq (comp f (id a)) f
    assoc : ∀{a b c d} (f : Hom c d) (g : Hom b c) (h : Hom a b)
      → Eq (comp (comp f g) h) (comp f (comp g h))

    comp-cong : ∀{a b c} {f f' : Hom b c} {g g' : Hom a b}
      → Eq f f'
      → Eq g g'
      → Eq (comp f g) (comp f' g')

  ---------------------------------------------------------------------------
  -- Cartesian
  ---------------------------------------------------------------------------

  field
    -- Product object and projections
    Prod : (a b : Ob) → Ob
    π₁    : ∀{a b} → Hom (Prod a b) a
    π₂    : ∀{a b} → Hom (Prod a b) b

  -- Properties of candidates for the pairing function

  IsPair₁ : ∀{a b c} (f : Hom c a) (h : Hom c (Prod a b)) → Set _
  IsPair₁ f h = Eq (comp π₁ h) f

  IsPair₂ : ∀{a b c} (g : Hom c b) (h : Hom c (Prod a b)) → Set _
  IsPair₂ g h = Eq (comp π₂ h) g

  field
    -- Pairing and β-laws
    pair : ∀{a b c} (f : Hom c a) (g : Hom c b) → Hom c (Prod a b)
    β-π₁  : ∀{a b c} {f : Hom c a} {g : Hom c b} → IsPair₁ f (pair f g)
    β-π₂  : ∀{a b c} {f : Hom c a} {g : Hom c b} → IsPair₂ g (pair f g)

    -- Uniqueness of pairing
    pair-unique : ∀{a b c} (f : Hom c a) (g : Hom c b) (h : Hom c (Prod a b))
      → IsPair₁ f h
      → IsPair₂ g h
      → Eq h (pair f g)

  ---------------------------------------------------------------------------
  field
    -- Terminal object
    Unit : Ob
    unit : ∀ a → Hom a Unit

    -- Uniqueness of terminal morphism
    unit-unique : ∀{a} (h : Hom a Unit)
      → Eq h (unit a)

  ---------------------------------------------------------------------------
  -- Closed
  ---------------------------------------------------------------------------

  -- Lift a morphism under a binder.
  -- lift f = f × id

  lift : ∀{a b} (f : Hom a b) {c} → Hom (Prod a c) (Prod b c)
  lift f = pair (comp f π₁) π₂

  field
    -- Exponential object and application
    Arr : (a b : Ob) → Ob
    apply : ∀{a b} → Hom (Prod (Arr a b) a) b

  IsCurry : ∀{a b c} (f : Hom (Prod c a) b) (h : Hom c (Arr a b)) → Set _
  IsCurry f h = Eq (comp apply (lift h)) f

  field
    curry   : ∀{a b c} (f : Hom (Prod c a) b) → Hom c (Arr a b)
    β-apply : ∀{a b c} (f : Hom (Prod c a) b) → IsCurry f (curry f)

    curry-unique : ∀{a b c} (f : Hom (Prod c a) b) (h : Hom c (Arr a b))
      → IsCurry f h
      → Eq h (curry f)

  ---------------------------------------------------------------------------
  -- Derived laws for products
  ---------------------------------------------------------------------------

  -- Congruence law for pairing

  pair-cong : ∀{a b c} {f f' : Hom c a} {g g' : Hom c b}
    → Eq f f'
    → Eq g g'
    → Eq (pair f g) (pair f' g')
  pair-cong {a} {b} {c} {f} {f'} {g} {g'} e e' = pair-unique f' g' (pair f g) ef eg
    where
    ef : Eq (comp π₁ (pair f g)) f'
    ef = eq-trans β-π₁ e
    eg : Eq (comp π₂ (pair f g)) g'
    eg = eq-trans β-π₂ e'

  -- Naturality law for pairing

  pair-nat : ∀{a b c d} (f : Hom c a) (g : Hom c b) (h : Hom d c)
    → Eq (comp (pair f g) h) (pair (comp f h) (comp g h))
  pair-nat {a} {b} {c} {d} f g h =
      pair-unique (comp f h) (comp g h) (comp (pair f g) h) ef eg
    where

    ef : Eq (comp π₁ (comp (pair f g) h)) (comp f h)
    ef = begin
      comp π₁ (comp (pair f g) h)   ≈⟨ eq-sym (assoc _ _ _) ⟩
      comp (comp π₁ (pair f g)) h   ≈⟨ comp-cong β-π₁ eq-refl ⟩
      comp f h                      ∎ where open EqR (Homs _ _)

    eg : Eq (comp π₂ (comp (pair f g) h)) (comp g h)
    eg = begin
      comp π₂ (comp (pair f g) h)   ≈⟨ eq-sym (assoc _ _ _) ⟩
      comp (comp π₂ (pair f g)) h   ≈⟨ comp-cong β-π₂ eq-refl ⟩
      comp g h                      ∎ where open EqR (Homs _ _)

  -- Lemma: id is a pairing of π₁ and π₂

  isPair-π₁-id : ∀{a b} → IsPair₁ π₁ (id (Prod a b))
  isPair-π₁-id {a} {b} = id-r _

  isPair-π₂-id : ∀{a b} → IsPair₂ π₂ (id (Prod a b))
  isPair-π₂-id {a} {b} = id-r _

  -- Thus, the pairing of π₁ and π₂ is the identity by uniqueness of pairing

  pair-π : ∀{a b} → Eq (pair π₁ π₂) (id (Prod a b))
  pair-π = eq-sym (pair-unique π₁ π₂ (id _) isPair-π₁-id isPair-π₂-id)

  ---------------------------------------------------------------------------
  -- Derived laws for lifting
  ---------------------------------------------------------------------------

  comp-lift-lift : ∀{a b c d} (f : Hom b c) (g : Hom a b)
    → Eq (comp (lift f) (lift g)) (lift (comp f g) {d})
  comp-lift-lift {a} {b} {c} {d} f g = begin
      comp (pair (comp f π₁) π₂) (pair (comp g π₁) π₂)  ≈⟨ pair-nat _ _ _ ⟩
      pair (comp (comp f π₁) (pair (comp g π₁) π₂))
           (comp π₂ (pair (comp g π₁) π₂))              ≈⟨ pair-cong (assoc _ _ _) β-π₂ ⟩
      pair (comp f (comp π₁ (pair (comp g π₁) π₂))) π₂  ≈⟨ pair-cong (comp-cong eq-refl β-π₁) eq-refl ⟩
      pair (comp f (comp g π₁)) π₂                      ≈⟨ pair-cong (eq-sym (assoc _ _ _)) eq-refl ⟩
      pair (comp (comp f g) π₁) π₂
      ∎ where open EqR (Homs _ _)

  lift-comp : ∀{a b c d} (f : Hom b c) (g : Hom a b)
    → Eq (lift (comp f g) {d}) (comp (lift f) (lift g))
  lift-comp {a} {b} {c} {d} f g = eq-sym (comp-lift-lift f g)

  ---------------------------------------------------------------------------
  -- Derived laws for exponentials
  ---------------------------------------------------------------------------

  -- Congruence law for currying

  curry-cong : ∀{a b c} {f f' : Hom (Prod c a) b}
    → (e : Eq f f')
    → Eq (curry f) (curry f')
  curry-cong {a} {b} {c} {f} {f'} e = curry-unique f' (curry f) eq
    where
    eq : Eq (comp apply (lift (curry f))) f'
    eq = eq-trans (β-apply f) e

  -- Naturality law for currying

  curry-nat : ∀{a b c d} (f : Hom (Prod c a) b) (h : Hom d c)
    → Eq (comp (curry f) h)
         (curry (comp f (lift h)))
  curry-nat {a} {b} {c} {d} f h =
      curry-unique (comp f (lift h)) (comp (curry f) h) eq
    where
    eq : Eq (comp apply (lift (comp (curry f) h)))
            (comp f (lift h))
    eq = begin
      comp apply (lift (comp (curry f) h))         ≈⟨ comp-cong eq-refl (lift-comp _ _) ⟩
      comp apply (comp (lift (curry f)) (lift h))  ≈⟨ eq-sym (assoc _ _ _) ⟩
      comp (comp apply (lift (curry f))) (lift h)  ≈⟨ comp-cong (β-apply _) eq-refl ⟩
      comp f (lift h) ∎ where open EqR (Homs _ _)


  -- Lemma: id is a currying of the apply morphism

  isCurry-apply-id : ∀ {a b} → IsCurry apply (id (Arr a b))
  isCurry-apply-id {a} {b} = begin
    comp apply (lift (id (Arr a b)))  ≈⟨ comp-cong eq-refl

     (begin′
      lift (id (Arr a b))             ≈⟨ pair-cong (id-l _) eq-refl ⟩′
      pair π₁ π₂                      ≈⟨ pair-π ⟩′
      id _
      ∎′ )⟩

    comp apply (id _)                 ≈⟨ id-r _ ⟩
    apply
    ∎ where
      open EqR (Homs _ _)
      open EqR (Homs _ _) using () renaming (begin_ to begin′_; _∎ to _∎′; _≈⟨_⟩_ to _≈⟨_⟩′_)

  -- Thus, curry apply is the identity by uniqueness of currying.

  curry-apply : ∀{a b} → Eq (curry apply) (id (Arr a b))
  curry-apply = eq-sym (curry-unique apply (id _) isCurry-apply-id)


-- Interpret the CCCInternalLanguage in an arbitrary CCC

module Sound {o m e} (C : CCC o m e) where

  open module Cat = CCC C using (Ob; Unit; Prod; Arr)

  open import Types
  open import CCCInternalLanguage

  ⟦_⟧ : Ty → Ob  -- \[[   \]]
  ⟦ 𝟙 ⟧     = Unit
  ⟦ a ⇒ b ⟧ = Arr ⟦ a ⟧ ⟦ b ⟧
  ⟦ a * b ⟧ = Prod ⟦ a ⟧ ⟦ b ⟧

  ⦅_⦆ : ∀{a b} → Hom a b → Cat.Hom ⟦ a ⟧ ⟦ b ⟧  -- \((  \))
  ⦅ id ⦆       = Cat.id _
  ⦅ f ∘ g ⦆    = Cat.comp ⦅ f ⦆ ⦅ g ⦆
  ⦅ fst ⦆      = Cat.π₁
  ⦅ snd ⦆      = Cat.π₂
  ⦅ pair f g ⦆ = Cat.pair ⦅ f ⦆ ⦅ g ⦆
  ⦅ unit ⦆     = Cat.unit _
  ⦅ curry f ⦆  = Cat.curry ⦅ f ⦆
  ⦅ apply ⦆    = Cat.apply

  ⟪_⟫ : ∀{a b} {f g : Hom a b} → f ~ g → Cat.Eq ⦅ f ⦆ ⦅ g ⦆  -- \<<  \>>
  ⟪ id-l ⟫          = Cat.id-l _
  ⟪ id-r ⟫          = Cat.id-r _
  ⟪ assoc ⟫         = Cat.assoc _ _ _
  ⟪ fst-pair ⟫      = Cat.β-π₁
  ⟪ snd-pair ⟫      = Cat.β-π₂
  ⟪ id-pair ⟫       = Cat.eq-sym Cat.pair-π
  ⟪ pair-comp ⟫     = Cat.pair-nat _ _ _
  ⟪ unit ⟫          = Cat.unit-unique _
  ⟪ apply-curry ⟫   = Cat.β-apply _
  ⟪ curry-apply ⟫   = Cat.curry-apply
  ⟪ curry-comp ⟫    = Cat.curry-nat _ _
  ⟪ eq-cong e e' ⟫  = Cat.comp-cong ⟪ e ⟫ ⟪ e' ⟫
  ⟪ eq-refl ⟫       = Cat.eq-refl
  ⟪ eq-sym e ⟫      = Cat.eq-sym ⟪ e ⟫
  ⟪ eq-trans e e' ⟫ = Cat.eq-trans ⟪ e ⟫ ⟪ e' ⟫
