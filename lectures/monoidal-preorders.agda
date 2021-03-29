{-# OPTIONS --prop #-}
module monoidal-preorders where

open import Level renaming (suc to _⁺) -- type \^+
open import Agda.Builtin.Bool
import Agda.Builtin.Equality as Equality
open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat renaming (Nat to ℕ) -- type \Bbb{N} or \bN

variable
  ℓ ℓ' ℓ''    : Level      -- type \ell
  A B C X Y   : Set ℓ
  P           : A → Prop ℓ
  φ χ ψ ω     : Prop ℓ
  f g h i     : A → B
  w x y z     : A
  p q r s     : Bool
  ws xs ys zs : List A
  k l m n     : ℕ

--8<--
infixl 6 _∧_  -- type \wedge or \and
infixl 6 _&_
infixl 6 _||_
infixl 6 _++_
infix  4 _≡_
infixr 4 _,_

data Squash (A : Set ℓ) : Prop ℓ where
  inc : A → Squash A

data Inc (A : Prop ℓ) : Set ℓ where
  inc : A → Inc A

_≡_ : (x y : A) → Prop _
x ≡ y = Squash (x Equality.≡ y)

pattern refl = inc Equality.refl

ap : (f : A → B) → x ≡ y → f x ≡ f y -- type \==, \equiv, or \eq
ap f refl = refl

subst : x ≡ y → P x → P y
subst refl p = p

postulate
  PropExt : (p : φ → ψ) → (q : ψ → φ) → φ ≡ ψ

record Setoid (A : Set ℓ) : Set (ℓ ⊔ ℓ' ⁺) where
  infix 4 _≈_ -- type \approx, \~~, or \eq

  field
    _≈_     : A → A → Prop ℓ'
    ≈-refl  : x ≈ x
    ≈-trans : x ≈ y → y ≈ z → x ≈ z
    ≈-sym   : x ≈ y → y ≈ x

module ReflexiveRelationReasoning (_R_ : A → A → Prop ℓ) (R-refl : ∀ {x} → x R x) where
  infix  4 begin_
  infixr 4 _≡⟨⟩_    -- type \<, \langle, or \(
  infixr 4 _≡⟨_⟩_
  infixr 4 _≡⁻¹⟨_⟩_ -- type \^- \^1
  infix  5 _∎       -- type \qed

  begin_ : x R y → x R y
  begin p = p

  _≡⟨⟩_ : ∀ x → x R y → x R y
  _ ≡⟨⟩ p = p

  _≡⟨_⟩_ : ∀ x → x ≡ y → y R z → x R z
  _ ≡⟨ refl ⟩ p = p

  _≡⁻¹⟨_⟩_ : ∀ x → y ≡ x → y R z → x R z
  _ ≡⁻¹⟨ refl ⟩ p = p

  _∎ : ∀ (x : A) → x R x
  _ ∎ = R-refl

module EqualityReasoning {ℓ} {A : Set ℓ} = ReflexiveRelationReasoning (_≡_ {A = A}) refl

module SetoidReasoning (S : Setoid {ℓ} {ℓ'} A) where
  open Setoid S

  infixr 4 _≈⟨_⟩_
  infixr 4 _≈⁻¹⟨_⟩_

  _≈⟨⟩_ : ∀ x → x ≈ y → x ≈ y
  _ ≈⟨⟩ p = p

  _≈⟨_⟩_ : ∀ x → x ≈ y → y ≈ z → x ≈ z
  _ ≈⟨ p ⟩ q = ≈-trans p q

  _≈⁻¹⟨_⟩_ : ∀ x → y ≈ x → y ≈ z → x ≈ z
  _ ≈⁻¹⟨ p ⟩ q = ≈-trans (≈-sym p) q

  open ReflexiveRelationReasoning _≈_ ≈-refl public
  open Setoid S using (_≈_) public

pattern T = true
pattern F = false -- type \perp or \bot

_&_ : (p q : Bool) → Bool
F & q = F
T & q = q

_||_ : (p q : Bool) → Bool
F || q = q
T || q = T

_++_ : (xs ys : List A) → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys -- type \::

data ∃ {A : Set ℓ} (P : A → Prop ℓ') : Prop (ℓ ⊔ ℓ') where -- type \ex or \exists
  _,_ : (a : A) → (p : P a) → ∃ P

record Unit : Set ℓ where
  constructor unit

record ⊤ : Prop ℓ where -- type \top
  constructor tt

record _×_ (A B : Set ℓ) : Set ℓ where
  constructor _,_
  field
    fst : A
    snd : B

record _∧_ (φ ψ : Prop ℓ) : Prop ℓ where
  constructor _,_
  field
    fst : φ
    snd : ψ
-->8--

record Preorder (A : Set ℓ) : Set (ℓ ⊔ ℓ' ⁺) where
  infix 4 _≤_ -- type \<=, \leqslant, \leq, or \le
  infix 4 _≥_ -- type \>=, \geqslant, \geq, or \ge

  field
    _≤_     : A → A → Prop ℓ'
    ≤-refl  : x ≤ x
    ≤-trans : x ≤ y → y ≤ z → x ≤ z

  _≥_ : A → A → Prop ℓ'
  x ≥ y = y ≤ x

-- Agda wizards, are these auxiliary definitions necessary for the syntax declarations?
private
  ≤-syntax = Preorder._≤_
  ≥-syntax = Preorder._≥_

infix 4 ≤-syntax
infix 4 ≥-syntax

syntax ≤-syntax P x y = x ≤[ P ] y
syntax ≥-syntax P x y = x ≥[ P ] y

module PreorderReasoning (P : Preorder {ℓ} {ℓ'} A) where
  open Preorder P

  infixr 4 _≤⟨_⟩_

  _≤⟨_⟩_ : ∀ x → x ≤ y → y ≤ z → x ≤ z
  _ ≤⟨ p ⟩ q = ≤-trans p q

  open ReflexiveRelationReasoning _≤_ ≤-refl public

module IsoReasoning (P : Preorder {ℓ} {ℓ'} A) where
  open Preorder P

  infix 4 _≅_ -- type \cong, \~=, or \eq

  private
    record _≅_ (x y : A) : Prop ℓ' where
      field
        ltr : x ≤ y
        rtl : x ≥ y
    open _≅_

    ≅-refl : x ≅ x
    ≅-refl .ltr = ≤-refl
    ≅-refl .rtl = ≤-refl

    ≅-trans : x ≅ y → y ≅ z → x ≅ z
    ≅-trans x≅y y≅z .ltr = ≤-trans (x≅y .ltr) (y≅z .ltr)
    ≅-trans x≅y y≅z .rtl = ≤-trans (y≅z .rtl) (x≅y .rtl)

    ≅-sym : x ≅ y → y ≅ x
    ≅-sym x≅y .ltr = x≅y .rtl
    ≅-sym x≅y .rtl = x≅y .ltr

    open Setoid

    ≅-setoid : Setoid A
    ≅-setoid ._≈_     = _≅_
    ≅-setoid .≈-refl  = ≅-refl
    ≅-setoid .≈-trans = ≅-trans
    ≅-setoid .≈-sym   = ≅-sym

  open SetoidReasoning ≅-setoid renaming (_≈_ to _≅_; _≈⟨⟩_ to _≅⟨⟩_; _≈⟨_⟩_ to _≅⟨_⟩_; _≈⁻¹⟨_⟩_ to _≅⁻¹⟨_⟩_) public

module ZigZagReasoning (P : Preorder {ℓ} {ℓ'} A) where
  open Preorder P

  infix  4 _∼_    -- type \sim
  infixr 4 _≤⟨_⟩_
  infixr 4 _≥⟨_⟩_

  private
    data _∼_ : A → A → Prop (ℓ ⊔ ℓ') where
      ∼-refl : x ∼ x
      ∼-zig  : (x≤y : x ≤ y) → (y∼z : y ∼ z) → x ∼ z
      ∼-zag  : (x≥y : x ≥ y) → (y∼z : y ∼ z) → x ∼ z

    zig : x ≤ y → x ∼ y
    zig x≤y = ∼-zig x≤y ∼-refl

    zag : x ≥ y → x ∼ y
    zag x≥y = ∼-zag x≥y ∼-refl

    ∼-trans : x ∼ y → y ∼ z → x ∼ z
    ∼-trans ∼-refl          y∼z = y∼z
    ∼-trans (∼-zig w≤x x∼y) y∼z = ∼-zig w≤x (∼-trans x∼y y∼z)
    ∼-trans (∼-zag w≥x x∼y) y∼z = ∼-zag w≥x (∼-trans x∼y y∼z)

    ∼-sym : x ∼ y → y ∼ x
    ∼-sym ∼-refl          = ∼-refl
    ∼-sym (∼-zig x≤y y∼z) = ∼-trans (∼-sym y∼z) (zag x≤y)
    ∼-sym (∼-zag x≥y y∼z) = ∼-trans (∼-sym y∼z) (zig x≥y)

    open Setoid

    ∼-setoid : Setoid A
    ∼-setoid ._≈_     = _∼_
    ∼-setoid .≈-refl  = ∼-refl
    ∼-setoid .≈-trans = ∼-trans
    ∼-setoid .≈-sym   = ∼-sym

  _≤⟨_⟩_ : ∀ x → x ≤ y → y ∼ z → x ∼ z
  _ ≤⟨ p ⟩ q = ∼-zig p q

  _≥⟨_⟩_ : ∀ x → x ≥ y → y ∼ z → x ∼ z
  _ ≥⟨ p ⟩ q = ∼-zag p q

  open SetoidReasoning ∼-setoid renaming (_≈_ to _∼_; _≈⟨⟩_ to _∼⟨⟩_; _≈⟨_⟩_ to _∼⟨_⟩_; _≈⁻¹⟨_⟩_ to _∼⁻¹⟨_⟩_) public

-- monotone function
record PreorderHom (P : Preorder {ℓ} {ℓ'} A) (Q : Preorder {ℓ} {ℓ'} B) : Set (ℓ ⊔ ℓ') where
  field
    fun        : A → B
    fun-pres-≤ : x ≤[ P ] y → fun x ≤[ Q ] fun y

-- Examples
module ExamplesPreorder where
  open Preorder

  -- Example 1. (ℕ,≤)
  infix 4 _≤ℕ_

  data _≤ℕ_ : ℕ → ℕ → Prop where
    ≤-zero :          0     ≤ℕ n
    ≤-suc  : m ≤ℕ n → suc m ≤ℕ suc n

  private    
    ≤ℕ-refl : n ≤ℕ n
    ≤ℕ-refl {n = 0}     = ≤-zero
    ≤ℕ-refl {n = suc _} = ≤-suc ≤ℕ-refl
    
    ≤ℕ-trans : k ≤ℕ l → l ≤ℕ m → k ≤ℕ m
    ≤ℕ-trans ≤-zero    q         = ≤-zero
    ≤ℕ-trans (≤-suc p) (≤-suc q) = ≤-suc (≤ℕ-trans p q)

  n≤suc-n : n ≤ℕ suc n
  n≤suc-n {0}     = ≤-zero
  n≤suc-n {suc _} = ≤-suc n≤suc-n

  Preorderℕ≤ : Preorder ℕ
  Preorderℕ≤ ._≤_     = _≤ℕ_
  Preorderℕ≤ .≤-refl  = ≤ℕ-refl
  Preorderℕ≤ .≤-trans = ≤ℕ-trans

  -- Example 2. (ℕ,∣)
  infix 4 _∣_ -- type \| or \mid

  _∣_ : (m n : ℕ) → Prop
  m ∣ n = ∃ λ k → k * m ≡ n

  private
    postulate
      *-assoc     : l * m * n ≡ l * (m * n)
      *-unit-left : 1 * n ≡ n

    ∣-refl : n ∣ n
    ∣-refl = 1 , *-unit-left

    ∣-trans : l ∣ m → m ∣ n → l ∣ n
    ∣-trans {l} {m} {n} (k , k*l≡m) (k' , k'*m≡n) = k' * k , k'*k*l≡n
      where
        open EqualityReasoning

        k'*k*l≡n : _
        k'*k*l≡n = k' * k * l ≡⟨ *-assoc {k'} {k} {l} ⟩ k' * (k * l) ≡⟨ ap (k' *_) k*l≡m ⟩ k' * m ≡⟨ k'*m≡n ⟩ n ∎

  Preorderℕ∣ : Preorder ℕ
  Preorderℕ∣ ._≤_     = _∣_
  Preorderℕ∣ .≤-refl  = ∣-refl
  Preorderℕ∣ .≤-trans = ∣-trans

  -- Example 3. (Bool,≤)
  infix 4 _≤Bool_

  data _≤Bool_ : Bool → Bool → Prop where
    ≤Bool-refl : p ≤Bool p
    false≤true : F ≤Bool T

  private
    ≤Bool-trans : p ≤Bool q → q ≤Bool r → p ≤Bool r
    ≤Bool-trans ≤Bool-refl p          = p
    ≤Bool-trans false≤true ≤Bool-refl = false≤true

  PreorderBool : Preorder Bool
  PreorderBool ._≤_     = _≤Bool_
  PreorderBool .≤-refl  = ≤Bool-refl
  PreorderBool .≤-trans = ≤Bool-trans

  -- Example 4. (List,⊆)
  module _ {A : Set ℓ} where
    infix 4 _∈_ -- type \in or \member
    infix 4 _⊆_ -- type \sub= or \subseteq

    data _∈_ (x : A) : List A → Prop ℓ where
      here  : x ∈ x ∷ xs
      there : x ∈ xs → x ∈ y ∷ xs

    _⊆_ : (xs ys : List A) → Prop ℓ
    xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

  module _ (A : Set ℓ) where
    private
      ⊆-refl : xs ⊆ xs
      ⊆-refl x∈xs = x∈xs -- = id

      ⊆-trans : xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
      ⊆-trans xs⊆ys ys⊆zs x∈xs = ys⊆zs (xs⊆ys x∈xs) -- = _∘_

    PreorderList : Preorder (List A)
    PreorderList ._≤_     = _⊆_
    PreorderList .≤-refl  = ⊆-refl
    PreorderList .≤-trans = ⊆-trans

  module _ (P : Preorder {ℓ} {ℓ'} A) where
    open Preorder P renaming (≤-refl to ≤P-refl; ≤-trans to ≤P-trans)

    -- Example 5. (P∞,≤)
    data _≤∞_ : Maybe A → Maybe A → Prop (ℓ ⊔ ℓ') where -- type \inf
      ≤∞-just : x ≤[ P ] y → just x ≤∞ just y
      ≤∞-∞    : x ≤∞ nothing

    private
      ≤∞-refl : x ≤∞ x
      ≤∞-refl {just x}  = ≤∞-just ≤P-refl
      ≤∞-refl {nothing} = ≤∞-∞

      ≤∞-trans : x ≤∞ y → y ≤∞ z → x ≤∞ z
      ≤∞-trans p             ≤∞-∞          = ≤∞-∞
      ≤∞-trans (≤∞-just x≤y) (≤∞-just y≤z) = ≤∞-just (≤P-trans x≤y y≤z)

    Preorder∞ : Preorder (Maybe A)
    Preorder∞ ._≤_     = _≤∞_
    Preorder∞ .≤-refl  = ≤∞-refl
    Preorder∞ .≤-trans = ≤∞-trans

    -- Example 6. (X → P,≤)
    module _ (X : Set) where
      _≤p_ : (X → A) → (X → A) → Prop ℓ'
      f ≤p g = ∀ {x} → f x ≤[ P ] g x

      private
        ≤p-refl : f ≤p f
        ≤p-refl = ≤P-refl

        ≤p-trans : f ≤p g → g ≤p h → f ≤p h
        ≤p-trans p q = ≤P-trans p q

      Preorderp : Preorder (X → A)
      Preorderp ._≤_         = _≤p_
      Preorderp .≤-refl  {f} = ≤p-refl {f}
      Preorderp .≤-trans     = ≤p-trans

  -- Example 7. (Prop,≤)
  module _ (ℓ : Level) where
    PreorderProp : Preorder (Prop ℓ)
    PreorderProp ._≤_     φ ψ   = φ → ψ
    PreorderProp .≤-refl  φ     = φ
    PreorderProp .≤-trans p q φ = q (p φ)

record CommMonoid (A : Set ℓ) : Set ℓ where
  infixl 6 _⊗_ -- type \ox or \otimes

  field
    -- A-set        : is-set A -- optional, ideal for future development
    I            : A                       -- monoid unit/monoidal unit
    _⊗_          : A → A → A               -- multiplication/monoidal product
    ⊗-assoc      : x ⊗ y ⊗ z ≡ x ⊗ (y ⊗ z) -- associativity
    ⊗-unit-left  : I ⊗ x ≡ x               -- unitality (1)
    ⊗-sym        : x ⊗ y ≡ y ⊗ x           -- commutativity/symmetry

  open EqualityReasoning

  ⊗-unit-right : x ⊗ I ≡ x -- unitality (2)
  ⊗-unit-right {x} = begin
      x ⊗ I
    ≡⟨ ⊗-sym ⟩
      I ⊗ x
    ≡⟨ ⊗-unit-left ⟩
      x ∎

-- Agda wizards, are these auxiliary definitions necessary for the syntax declarations?
private
  I-syntax = CommMonoid.I
  ⊗-syntax = CommMonoid._⊗_

infixl 6 ⊗-syntax

syntax I-syntax M     = I^ M
syntax ⊗-syntax M x y = x ⊗[ M ] y

-- Examples (continued)
module ExamplesMonoid where
  open ExamplesPreorder public
  open CommMonoid

  -- Example 8. (ℕ,+)
  private
    postulate
      +-assoc : l + m + n ≡ l + (m + n)
      +-comm  : m + n ≡ n + m

    +-unit-left : 0 + n ≡ n
    +-unit-left = refl

  Monoidℕ+ : CommMonoid ℕ
  Monoidℕ+ .I                   = 0
  Monoidℕ+ ._⊗_                 = _+_
  Monoidℕ+ .⊗-assoc {l} {m} {n} = +-assoc {l} {m} {n}
  Monoidℕ+ .⊗-unit-left         = +-unit-left
  Monoidℕ+ .⊗-sym {m} {n}       = +-comm {m} {n}

  -- Example 9. (ℕ,*)
  private
    postulate
      *-assoc     : l * m * n ≡ l * (m * n)
      *-comm      : m * n ≡ n * m
      *-unit-left : 1 * n ≡ n

  Monoidℕ* : CommMonoid ℕ
  Monoidℕ* .I                   = 1
  Monoidℕ* ._⊗_                 = _*_
  Monoidℕ* .⊗-assoc {l} {m} {n} = *-assoc {l} {m} {n}
  Monoidℕ* .⊗-unit-left         = *-unit-left
  Monoidℕ* .⊗-sym {m} {n}       = *-comm {m} {n}

  -- Example 10. (Bool,&)
  private
    postulate
      &-assoc : p & q & r ≡ p & (q & r)
      &-comm  : p & q ≡ q & p

    &-unit-left : T & p ≡ p
    &-unit-left = refl

  MonoidBool& : CommMonoid Bool
  MonoidBool& .I                   = T
  MonoidBool& ._⊗_                 = _&_
  MonoidBool& .⊗-assoc {p} {q} {r} = &-assoc {p} {q} {r}
  MonoidBool& .⊗-unit-left         = &-unit-left
  MonoidBool& .⊗-sym {p} {q}       = &-comm {p} {q}

  -- Example 11. (Bool,||)
  private
    postulate
      ||-assoc : p || q || r ≡ p || (q || r)
      ||-comm  : p || q ≡ q || p

    ||-unit-left : F || p ≡ p
    ||-unit-left = refl

  MonoidBool|| : CommMonoid Bool
  MonoidBool|| .I                   = F
  MonoidBool|| ._⊗_                 = _||_
  MonoidBool|| .⊗-assoc {p} {q} {r} = ||-assoc {p} {q} {r}
  MonoidBool|| .⊗-unit-left         = ||-unit-left
  MonoidBool|| .⊗-sym {p} {q}       = ||-comm {p} {q}

  -- Non-Example 12. (List,++)
  module _ {A : Set ℓ} where
    private
      postulate
        ++-assoc : xs ++ ys ++ zs ≡ xs ++ (ys ++ zs)

      ++-unit-left : [] ++ xs ≡ xs
      ++-unit-left = refl

    MonoidList++ : CommMonoid (List A)
    MonoidList++ .I                      = []
    MonoidList++ ._⊗_                    = _++_
    MonoidList++ .⊗-assoc {xs} {ys} {zs} = ++-assoc {ℓ} {A} {xs} {ys} {zs}
    MonoidList++ .⊗-unit-left            = ++-unit-left
    MonoidList++ .⊗-sym {xs} {ys}        = {!!}

  module _ (M : CommMonoid A) where
    -- Example 13. (M∞,⊗)
    private
      infixl 6 _⊗∞_

      I∞ : Maybe A
      I∞ = just (I^ M)

      _⊗∞_ : (x y : Maybe A) → Maybe A
      just x  ⊗∞ just y  = just (x ⊗[ M ] y)
      just x  ⊗∞ nothing = nothing
      nothing ⊗∞ _       = nothing

      postulate
        ⊗∞-assoc      : x ⊗∞ y ⊗∞ z ≡ x ⊗∞ (y ⊗∞ z)
        ⊗∞-unit-left  : I∞ ⊗∞ x ≡ x
        ⊗∞-unit-right : x ⊗∞ I∞ ≡ x
        ⊗∞-sym        : x ⊗∞ y ≡ y ⊗∞ x

    Monoid∞ : CommMonoid (Maybe A)
    Monoid∞ .I           = I∞
    Monoid∞ ._⊗_         = _⊗∞_
    Monoid∞ .⊗-assoc     = ⊗∞-assoc
    Monoid∞ .⊗-unit-left = ⊗∞-unit-left
    Monoid∞ .⊗-sym       = ⊗∞-sym

    -- Example 14. (X → M,⊗)
    module _ (X : Set) where
      private
        infixl 6 _⊗p_

        Ip : X → A
        Ip = λ x → I^ M

        _⊗p_ : (x y : X → A) → X → A
        f ⊗p g = λ x → f x ⊗[ M ] g x

        postulate
          ⊗p-assoc      : x ⊗p y ⊗p z ≡ x ⊗p (y ⊗p z)
          ⊗p-unit-left  : Ip ⊗p x ≡ x
          ⊗p-unit-right : x ⊗p Ip ≡ x
          ⊗p-sym        : x ⊗p y ≡ y ⊗p x

      Monoidp : CommMonoid (X → A)
      Monoidp .I           = Ip
      Monoidp ._⊗_         = _⊗p_
      Monoidp .⊗-assoc     = ⊗p-assoc
      Monoidp .⊗-unit-left = ⊗p-unit-left
      Monoidp .⊗-sym       = ⊗p-sym

  -- Example 15. (Prop,∧)
  module _ (ℓ : Level) where
    private
      ∧-assoc : φ ∧ χ ∧ ψ ≡ φ ∧ (χ ∧ ψ)
      ∧-assoc = PropExt ltr rtl
        where
          ltr = λ { ((φ , χ) , ψ) → ( φ , χ  , ψ) }
          rtl = λ { ( φ , χ  , ψ) → ((φ , χ) , ψ) }

      ∧-unit-left : ⊤ ∧ φ ≡ φ
      ∧-unit-left = PropExt ltr rtl
        where
          ltr = λ { (_ , φ) → φ        }
          rtl = λ { φ       → (tt , φ) }

      ∧-sym : φ ∧ ψ ≡ ψ ∧ φ
      ∧-sym = PropExt ltr rtl
        where
          ltr = λ { (φ , ψ) → (ψ , φ) }
          rtl = λ { (ψ , φ) → (φ , ψ) }

    MonoidProp∧ : CommMonoid (Prop ℓ)
    MonoidProp∧ .I           = ⊤
    MonoidProp∧ ._⊗_ φ ψ     = φ ∧ ψ
    MonoidProp∧ .⊗-assoc     = ∧-assoc
    MonoidProp∧ .⊗-unit-left = ∧-unit-left
    MonoidProp∧ .⊗-sym       = ∧-sym

-- monoid homomorphism
record MonoidHom (M : CommMonoid {ℓ} A) (N : CommMonoid {ℓ} B) : Set ℓ where
  field
    fun        : A → B
    fun-pres-I : fun (I^ M) ≡ I^ N
    fun-pres-⊗ : ∀ {x} {y} → fun (x ⊗[ M ] y) ≡ fun x ⊗[ N ] fun y

-- symmetric monoidal preorder
record SymMonPre (P : Preorder {ℓ} {ℓ'} A) : Set (ℓ ⊔ ℓ') where
  field
    ⊗-structure : CommMonoid A

  open Preorder P
  open CommMonoid ⊗-structure

  field
    ⊗-mono : x ≤ z → y ≤ w → x ⊗ y ≤ z ⊗ w

  open CommMonoid ⊗-structure public

record CarMonPre (P : Preorder {ℓ} {ℓ'} A) : Set (ℓ ⊔ ℓ') where
  infixl 6 _⊗_

  field
    I            : A
    _⊗_          : A → A → A
    ⊗-unit-left  : I ⊗ x ≡ x
    ⊗-unit-right : x ⊗ I ≡ x

  open Preorder P

  field
    ⊗-mono    : x ≤ z → y ≤ w → x ⊗ y ≤ z ⊗ w
    ⊗-discard : x ≤ I
    ⊗-copy    : x ≤ x ⊗ x

  open PreorderReasoning P

  ⊗-fst : x ⊗ y ≤ x
  ⊗-fst {x} {y} = x ⊗ y ≤⟨ ⊗-mono ≤-refl ⊗-discard ⟩ x ⊗ I ≡⟨ ⊗-unit-right ⟩ x ∎

  postulate
    ⊗-snd   : x ⊗ y ≤ y
    ⊗-prd   : x ≤ y → x ≤ z → x ≤ y ⊗ z
    ⊗-assoc : x ⊗ y ⊗ z ≡ x ⊗ (y ⊗ z)
    ⊗-sym   : x ⊗ y ≡ y ⊗ x

module _ {P : Preorder {ℓ} {ℓ'} A} (S₁ : CarMonPre P) (S₂ : CarMonPre P) where -- type \_1 and \_2
  open CarMonPre
  open CarMonPre S₁ using () renaming (I to I₁; _⊗_ to _⊗₁_)
  open CarMonPre S₂ using () renaming (I to I₂; _⊗_ to _⊗₂_)
  open IsoReasoning P

  postulate
    ⊗-unique : x ⊗₁ y ≅ x ⊗₂ y

  I-unique : I₁ ≅ I₂
  I-unique = I₁ ≡⁻¹⟨ S₂ .⊗-unit-right ⟩ I₁ ⊗₂ I₂ ≅⁻¹⟨ ⊗-unique ⟩ I₁ ⊗₁ I₂ ≡⟨ S₁ .⊗-unit-left ⟩ I₂ ∎

-- Examples (continued)
module ExamplesMonoidal where
  open ExamplesMonoid public
  open SymMonPre

  module _ where
    open Preorder Preorderℕ≤

    -- Example 16. (ℕ,≤,+)
    n≤m+n : n ≤ m + n
    n≤m+n {m = zero}  = ≤-refl
    n≤m+n {m = suc _} = ≤-trans n≤m+n n≤suc-n

    private
      +-mono : k ≤ l → m ≤ n → k + m ≤ l + n
      +-mono ≤-zero    q = ≤-trans q n≤m+n
      +-mono (≤-suc p) q = ≤-suc (+-mono p q)

    SymMonPreℕ≤+ : SymMonPre Preorderℕ≤
    SymMonPreℕ≤+ .⊗-structure = Monoidℕ+
    SymMonPreℕ≤+ .⊗-mono      = +-mono

    -- Example 17. (ℕ,≤,*)
    private
      *-mono : k ≤ l → m ≤ n → k * m ≤ l * n
      *-mono ≤-zero    q = ≤-zero
      *-mono (≤-suc p) q = +-mono q (*-mono p q)

    SymMonPreℕ≤* : SymMonPre Preorderℕ≤
    SymMonPreℕ≤* .⊗-structure = Monoidℕ*
    SymMonPreℕ≤* .⊗-mono      = *-mono

  module _ where
    -- Example 18. (ℕ,∣,*)
    private
      postulate
        *-mono : k ∣ l → m ∣ n → k * m ∣ l * n

    SymMonPreℕ∣* : SymMonPre Preorderℕ∣
    SymMonPreℕ∣* .⊗-structure = Monoidℕ*
    SymMonPreℕ∣* .⊗-mono      = *-mono

  module _ where
    open Preorder PreorderBool

    -- Example 19. (Bool,≤,&)
    private
      postulate
        &-mono : p ≤ q → r ≤ s → p & r ≤ q & s

    SymMonPreBool& : SymMonPre PreorderBool
    SymMonPreBool& .⊗-structure = MonoidBool&
    SymMonPreBool& .⊗-mono      = &-mono

    -- Example 20. (Bool,≤,||)
    private
      postulate
        ||-mono : p ≤ q → r ≤ s → p || r ≤ q || s

    SymMonPreBool|| : SymMonPre PreorderBool
    SymMonPreBool|| .⊗-structure = MonoidBool||
    SymMonPreBool|| .⊗-mono      = ||-mono

  -- Non-Example 21. (List,⊆,++)
  module _ (A : Set ℓ) where
    private
      postulate
        ++-mono : ws ⊆ xs → ys ⊆ zs → ws ++ ys ⊆ xs ++ zs

    SymMonPreList++ : SymMonPre (PreorderList A)
    SymMonPreList++ .⊗-structure = MonoidList++
    SymMonPreList++ .⊗-mono      = ++-mono

  module _ (P : Preorder {ℓ} {ℓ'} A) (M : CommMonoid A) where
    -- Example 22. (P∞,≤,⊗)
    private
      P∞ = Preorder∞ P
      M∞ = Monoid∞ M

      postulate
        ∞-mono : w ≤[ P∞ ] x → y ≤[ P∞ ] z → w ⊗[ M∞ ] y ≤[ P∞ ] x ⊗[ M∞ ] z

    SymMonPre∞ : SymMonPre (Preorder∞ P)
    SymMonPre∞ .⊗-structure = Monoid∞ M
    SymMonPre∞ .⊗-mono      = ∞-mono

    -- Example 23. (X → P,≤,⊗)
    module _ (X : Set) where
      private
        Pp = Preorderp P X
        Mp = Monoidp M X

        postulate
          p-mono : f ≤[ Pp ] g → h ≤[ Pp ] i → f ⊗[ Mp ] h ≤[ Pp ] g ⊗[ Mp ] i

      SymMonPrep : SymMonPre (Preorderp P X)
      SymMonPrep .⊗-structure = Monoidp M X
      SymMonPrep .⊗-mono      = p-mono

  -- Example 24. (Prop,≤,∧)
  module _ (ℓ : Level) where
    open Preorder (PreorderProp ℓ)

    private
      ∧-mono : φ ≤ χ → ψ ≤ ω → φ ∧ ψ ≤ χ ∧ ω
      ∧-mono p q (φ , ψ) = p φ , q ψ

    SymMonPreProp∧ : SymMonPre (PreorderProp ℓ)
    SymMonPreProp∧ .⊗-structure = MonoidProp∧ ℓ
    SymMonPreProp∧ .⊗-mono      = ∧-mono

-- V-enriched category for V = (A, P, S)
module _ {A : Set ℓ} (P : Preorder {ℓ} {ℓ'} A) (S : SymMonPre P) (ℓ'' : Level) where
  open Preorder P          -- _≤_
  open PreorderReasoning P -- _≤⟨_⟩_ and ∎
  open SymMonPre S         -- I and _⊗_

  record _,_-Category_ : Set (ℓ ⊔ ℓ' ⊔ ℓ'' ⁺) where
    field
      Obj : Set ℓ''
      Hom : Obj → Obj → A
      id  : ∀ (x : Obj) → I ≤ Hom x x
      ∘   : ∀ {x y z : Obj} → Hom y z ⊗ Hom x y ≤ Hom x z

    ; : ∀ {x y z : Obj} → Hom x y ⊗ Hom y z ≤ Hom x z
    ; {x} {y} {z} = begin
        Hom x y ⊗ Hom y z
      ≡⟨ ⊗-sym ⟩
        Hom y z ⊗ Hom x y
      ≤⟨ ∘ ⟩
        Hom x z ∎

-- the one-to-one correspondence between preorders and Prop-enriched
-- categories (cf. Theorem 2.49 in Seven Sketches)
module _ where
  module _ (Q : Preorder {ℓ} {ℓ'} B) where
    open ExamplesMonoid  using (PreorderProp)
    open ExamplesMonoidal using (SymMonPreProp∧)

    open Preorder Q

    open _,_-Category_

    Preorder-to-SymMonPre : PreorderProp ℓ' , SymMonPreProp∧ ℓ' -Category ℓ
    Preorder-to-SymMonPre .Obj           = B
    Preorder-to-SymMonPre .Hom x y       = x ≤ y
    Preorder-to-SymMonPre .id _          = λ _ → ≤-refl
    Preorder-to-SymMonPre .∘ (y≤z , x≤y) = ≤-trans x≤y y≤z

  module _ where
    open ExamplesMonoid   using (PreorderProp)
    open ExamplesMonoidal using (SymMonPreProp∧)

    module _ (C : PreorderProp ℓ' , SymMonPreProp∧ ℓ' -Category ℓ) where
      open _,_-Category_ C

      open Preorder

      SymMonPre-to-Preorder : Preorder Obj
      SymMonPre-to-Preorder ._≤_             = Hom
      SymMonPre-to-Preorder .≤-refl          = id _ tt
      SymMonPre-to-Preorder .≤-trans x≤y y≤z = ; (x≤y , y≤z)

  module _ (Q : Preorder {ℓ} {ℓ'} B) where
    _ : SymMonPre-to-Preorder (Preorder-to-SymMonPre Q) ≡ Q
    _ = refl

  module _ where
    open ExamplesMonoid  using (PreorderProp)
    open ExamplesMonoidal using (SymMonPreProp∧)

    module _ (C : PreorderProp ℓ' , SymMonPreProp∧ ℓ' -Category ℓ) where
      _ : Preorder-to-SymMonPre (SymMonPre-to-Preorder C) ≡ C
      _ = refl
