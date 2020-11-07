-- Simple types

data Ty : Set where
  𝟙    : Ty                -- \b1
  _⇒_ : (a b : Ty) → Ty   -- \r2
  _*_ :  (a b : Ty) → Ty

-- Typing contexts

data Cxt : Set where
  ε   : Cxt
  _,_ : (Γ : Cxt) (a : Ty) → Cxt

infix 19 _∈_

data _∈_ (a : Ty) : (Γ : Cxt) → Set where
  𝟘   : {Γ : Cxt} → a ∈ Γ , a
  𝟙+_ : {Γ : Cxt} {b : Ty} → a ∈ Γ → a ∈ Γ , b

-- Subset relation

infix 19 _⊆_ -- \sub=

_⊆_ : (Γ Δ : Cxt) → Set
Γ ⊆ Δ = ∀ {a} → a ∈ Γ → a ∈ Δ

sub-refl : ∀ {Γ} → Γ ⊆ Γ
sub-refl x = x

sub-trans : ∀ {Γ Δ Ε} → Γ ⊆ Δ → Δ ⊆ Ε → Γ ⊆ Ε
sub-trans f g x = g (f x)

sub-wk : ∀ {Γ a} → Γ ⊆ Γ , a
sub-wk = 𝟙+_

sub-drop : ∀ {Γ Δ a} → Γ ⊆ Δ → Γ ⊆ Δ , a
sub-drop f = sub-trans f sub-wk

sub-keep : ∀ {Γ Δ a} → Γ ⊆ Δ → Γ , a ⊆ Δ , a
sub-keep f 𝟘      = 𝟘
sub-keep f (𝟙+ x) = 𝟙+ f x

-- Prefix relation

infix 19 _≼_ -- \preceq

data _≼_ (Γ : Cxt) : (Δ : Cxt) → Set where
  pre-drop  : {Δ : Cxt} {a : Ty} → Γ ≼ Δ → Γ ≼ Δ , a

  pre-refl  : Γ ≼ Γ

pre-sub : ∀ {Γ Δ} → Γ ≼ Δ → Γ ⊆ Δ
pre-sub pre-refl        = sub-refl
pre-sub (pre-drop x)    = sub-drop (pre-sub x)

pre-trans : ∀ {Γ Δ Ε} → Γ ≼ Δ → Δ ≼ Ε → Γ ≼ Ε
pre-trans x pre-refl     = x
pre-trans x (pre-drop y) = pre-drop (pre-trans x y)

pre-wk : ∀ {Γ a} → Γ ≼ Γ , a
pre-wk = pre-drop pre-refl

-- Notation

zero : ∀ {Γ} → Γ ≼ Γ
zero = pre-refl

succ : ∀ {Γ Δ a} → Γ ≼ Δ → Γ ≼ Δ , a
succ = pre-drop

_+_ = pre-trans

_+1 = succ

1+_ : ∀ {Γ Δ a} → Γ , a ≼ Δ → Γ ≼ Δ
1+_ = succ zero +_

_⊕_ = pre-sub
