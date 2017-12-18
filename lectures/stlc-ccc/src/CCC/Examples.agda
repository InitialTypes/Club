------------------------------------------------------------------------
-- Some instances of CCCs
------------------------------------------------------------------------

module CCC.Examples where

open import Agda.Primitive  -- Universe levels
open import Data.Product as Prod using (_,_; proj₁; proj₂; _×_; <_,_>)
import Function as Fun
import Function.Equality as SetoidFun
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
import Relation.Binary.OrderMorphism as Ord

open import CCC
open import Types
import CCCInternalLanguage as Internal


------------------------------------------------------------------------
-- The internal language of CCCs forms a CCC

Internal-CCC : CCC _ _ _
Internal-CCC = record

  -- Objects and morphisms.
  { Ob   = Ty
  ; Homs = homSetoid

  -- Category operations
  ; id   = λ _ → id
  ; comp = _∘_

  -- Category laws
  ; id-l  = λ _ → id-l
  ; id-r  = λ _ → id-r
  ; assoc = λ _ _ _ → assoc

  ; comp-cong = eq-comp

  -- Product object and projections
  ; Prod = _*_
  ; π₁   = fst
  ; π₂   = snd

  -- Pairing and β-laws
  ; pair = pair
  ; β-π₁ = fst-pair
  ; β-π₂ = snd-pair

  -- Uniqueness of pairing
  ; pair-unique = pair-unique

  -- Terminal object
  ; Unit = 𝟙
  ; unit = λ _ → unit

  -- Uniqueness of terminal morphism
  ; unit-unique = λ _ → unit

  -- Exponential object and application
  ; Arr   = _⇒_
  ; apply = apply

  -- Currying and the computation law for application
  ; curry        = curry
  ; β-apply      = λ _ → apply-curry

  -- Uniqueness of curry
  ; curry-unique = curry-unique
  }
  where open Internal


------------------------------------------------------------------------
-- A universe-polymorphic unit type in Agda

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


------------------------------------------------------------------------
-- Cartesian products over setoids

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


------------------------------------------------------------------------
-- Preorder morphisms, products, etc.

module Pre where

  open Preorder renaming (_∼_ to _≤_)

  -- The setoid underlying a preorder

  ⌊_⌋ : ∀ {p₁ p₂ p₃} → Preorder p₁ p₂ p₃ → Setoid p₁ p₂
  ⌊ P ⌋ = record
    { Carrier       = P.Carrier
    ; _≈_           = P._≈_
    ; isEquivalence = P.isEquivalence
    }
    where module P = Preorder P

  infixr 0 _⟶_

  -- Preorder morphisms (adapted from Relation.Binary.OrderMorphism)
  record _⟶_ {p₁ p₂ p₃ q₁ q₂ q₃}
             (P : Preorder p₁ p₂ p₃)
             (Q : Preorder q₁ q₂ q₃) : Set (p₁ ⊔ p₂ ⊔ p₃ ⊔ q₁ ⊔ q₂ ⊔ q₃) where
    infixl 5 _⟨$⟩_
    field
      _⟨$⟩_    : Carrier P → Carrier Q
      cong     : _≈_ P =[ _⟨$⟩_ ]⇒ _≈_ Q
      monotone : _≤_ P =[ _⟨$⟩_ ]⇒ _≤_ Q

    -- The underlying setoid map
    setoidMap : ⌊ P ⌋ SetoidFun.⟶ ⌊ Q ⌋
    setoidMap = record
      { _⟨$⟩_ = _⟨$⟩_
      ; cong  = cong
      }

  open _⟶_

  id : ∀ {p₁ p₂ p₃} {P : Preorder p₁ p₂ p₃} → P ⟶ P
  id = record
    { _⟨$⟩_    = Fun.id
    ; cong     = Fun.id
    ; monotone = Fun.id
    }

  infixr 9 _∘_

  _∘_ : ∀ {p₁ p₂ p₃ q₁ q₂ q₃ r₁ r₂ r₃}
          {P : Preorder p₁ p₂ p₃}
          {Q : Preorder q₁ q₂ q₃}
          {R : Preorder r₁ r₂ r₃} →
        Q ⟶ R → P ⟶ Q → P ⟶ R
  f ∘ g = record
    { _⟨$⟩_    = Fun._∘_ (f ⟨$⟩_)     (g ⟨$⟩_)
    ; cong     = Fun._∘_ (cong f)     (cong g)
    ; monotone = Fun._∘_ (monotone f) (monotone g)
    }


  infixr 0 _⇨_

  -- The preorder of preorder morphisms
  _⇨_ : ∀ {p₁ p₂ p₃ q₁ q₂ q₃} →
        Preorder p₁ p₂ p₃ → Preorder q₁ q₂ q₃ → Preorder _ _ _
  P ⇨ Q = record
    { Carrier = P ⟶ Q
    ; _≈_     = λ f g → ∀ {x y} → x ≈₁ y → f ⟨$⟩ x ≈₂ g ⟨$⟩ y
    ; _∼_     = λ f g → ∀ {x} → f ⟨$⟩ x ≤₂ g ⟨$⟩ x
    ; isPreorder = record
      { isEquivalence = record
        { refl  = λ {f} → cong f
        ; sym   = λ f≈g x≈y → Q.Eq.sym (f≈g (P.Eq.sym x≈y))
        ; trans = λ f≈g g≈h x≈y → Q.Eq.trans (f≈g P.Eq.refl) (g≈h x≈y)
        }
      ; reflexive = λ f≈g → Q.reflexive (f≈g P.Eq.refl)
      ; trans     = λ f≤g g≤h → Q.trans f≤g g≤h
      }
    }
    where
      open module P = Preorder P using () renaming (_≈_ to _≈₁_; _∼_ to _≤₁_)
      open module Q = Preorder Q using () renaming (_≈_ to _≈₂_; _∼_ to _≤₂_)

  -- The order on P ⟶ Q defined in P ⇨ Q is just the point-wise
  -- lifting of Q.  Thanks to monotonicity, this is equivalent to a
  -- more relaxed definition modulo P on inputs.
  relax : ∀ {p₁ p₂ p₃ q₁ q₂ q₃}
          {P : Preorder p₁ p₂ p₃} {Q : Preorder q₁ q₂ q₃} (f g : P ⟶ Q) →
          _≤_ (P ⇨ Q) f g → ∀ {x y} → _≤_ P x y → _≤_ Q (f ⟨$⟩ x) (g ⟨$⟩ y)
  relax {Q = Q} f g f≤g x≤y = trans Q (monotone f x≤y) f≤g

  -- The unit type forms a terminal preorder with the trivial relation.

  ⊤-preorder : ∀ {p₁ p₂ p₃} → Preorder p₁ p₂ p₃
  ⊤-preorder = record
    { Carrier       = ⊤
    ; _≈_           = λ _ _ → ⊤
    ; _∼_           = λ _ _ → ⊤
    ; isPreorder    = record
      { isEquivalence = record
        { refl    = tt
        ; sym     = λ _   → tt
        ; trans   = λ _ _ → tt
        }
      ; reflexive = λ _   → tt
      ; trans     = λ _ _ → tt
      }
    }

  -- The unique map into the terminal preorder
  ⊤-intro' : ∀ {p₁ p₂ p₃} → (P : Preorder p₁ p₂ p₃) →
             P ⟶ ⊤-preorder {p₁} {p₂} {p₃}
  ⊤-intro' s = record
    { _⟨$⟩_    = λ _ → tt
    ; cong     = λ _ → tt
    ; monotone = λ _ → tt
    }

  -- The product of two preorders.

  _×'_ : ∀ {p₁ p₂ p₃ q₁ q₂ q₃} → Preorder p₁ p₂ p₃ → Preorder q₁ q₂ q₃ →
         Preorder (p₁ ⊔ q₁) (p₂ ⊔ q₂) (p₃ ⊔ q₃)
  P ×' Q = record
    { Carrier = Carrier P × Carrier Q
    ; _≈_     = _≈_ P ⊗ _≈_ Q
    ; _∼_     = _≤_ P ⊗ _≤_ Q
    ; isPreorder = record
      { isEquivalence = ⊗-isEquivalence (isEquivalence P) (isEquivalence Q)
      ; reflexive     = Prod.map (reflexive P) (reflexive Q)
      ; trans         = Prod.zip (trans P) (trans Q)
      }
    }

  -- Projection and pairing mpps

  π₁ : ∀ {p₁ p₂ p₃ q₁ q₂ q₃} {P : Preorder p₁ p₂ p₃} {Q : Preorder q₁ q₂ q₃} →
       P ×' Q ⟶ P
  π₁ = record { _⟨$⟩_ = proj₁ ; cong = proj₁ ; monotone = proj₁ }

  π₂ : ∀ {p₁ p₂ p₃ q₁ q₂ q₃} {P : Preorder p₁ p₂ p₃} {Q : Preorder q₁ q₂ q₃} →
       P ×' Q ⟶ Q
  π₂ = record { _⟨$⟩_ = proj₂ ; cong = proj₂ ; monotone = proj₂ }

  <_,_>' : ∀ {p₁ p₂ p₃ q₁ q₂ q₃ r₁ r₂ r₃} {P : Preorder p₁ p₂ p₃}
           {Q : Preorder q₁ q₂ q₃} {R : Preorder r₁ r₂ r₃} →
           (P ⟶ Q) → (P ⟶ R) → P ⟶ Q ×' R
  < f , g >' = record
    { _⟨$⟩_    = < f ⟨$⟩_ , g ⟨$⟩_ >
    ; cong     = < cong f , cong g >
    ; monotone = < monotone f , monotone g >
    }

  -- Currying pnd uncurrying mpps

  curry' : ∀ {p₁ p₂ p₃ q₁ q₂ q₃ r₁ r₂ r₃} {P : Preorder p₁ p₂ p₃}
           {Q : Preorder q₁ q₂ q₃} {R : Preorder r₁ r₂ r₃} →
           (P ×' Q ⟶ R) → (P ⟶ Q ⇨ R)
  curry' {P = P} {Q} f = record
    { _⟨$⟩_ = λ x → record
      { _⟨$⟩_    = λ y     → f ⟨$⟩ (x , y)
      ; cong     = λ y₁≈y₂ → cong f (Eq.refl P , y₁≈y₂)
      ; monotone = λ y₁≤y₂ → monotone f (refl P , y₁≤y₂)
      }
    ; cong     = λ x₁≈x₂ y₁≈y₂ → cong f (x₁≈x₂ , y₁≈y₂)
    ; monotone = λ x₁≤x₂ → monotone f (x₁≤x₂ , refl Q)
    }


------------------------------------------------------------------------
-- (Small) preorders and order-preserving maps form a CCC

Pre-CCC : ∀ {a} → CCC (lsuc a) _ _
Pre-CCC {a} = record

  -- Objects and morphisms.
  { Ob   = Preorder a a a
  ; Homs = λ a b → ⌊ a ⇨ b ⌋

  -- Category operations
  ; id   = λ _ → id
  ; comp = _∘_

  -- Category laws
  ; id-l  = λ f → cong f
  ; id-r  = λ f → cong f
  ; assoc = λ f g h → cong (f ∘ g ∘ h)

  ; comp-cong = λ f≈f' g≈g' x≈y → f≈f' (g≈g' x≈y)

  -- Product object and projections
  ; Prod = _×'_
  ; π₁   = π₁
  ; π₂   = π₂

  -- Pairing and β-laws
  ; pair = <_,_>'
  ; β-π₁ = λ {a b c f g} → f .cong
  ; β-π₂ = λ {a b c f g} → g .cong

  -- Uniqueness of pairing
  ; pair-unique = λ f g h eq₁ eq₂ → < eq₁ , eq₂ >

  -- Terminal object
  ; Unit = ⊤-preorder
  ; unit = ⊤-intro'

  -- Uniqueness of terminal morphism
  ; unit-unique = λ h _ → tt

  -- Exponential object and application
  ; Arr   = _⇨_
  ; apply = record
    { _⟨$⟩_    = λ{ (f , x)     → f ⟨$⟩ x }
    ; cong     = λ{ (f≈g , x≈y) → f≈g x≈y }
    ; monotone = λ{ {f , x} {g , y} (f≤g , x≤y) → relax f g f≤g x≤y }
    }

  -- Currying and the computation law for application
  ; curry        = curry'
  ; β-apply      = λ f → cong f

  -- Uniqueness of curry
  ; curry-unique = λ f h hyp x₁≈x₂ y₁≈y₂ → hyp (x₁≈x₂ , y₁≈y₂)
  }
  where
    open Pre
    open _⟶_
