-- A sound interpreter for Gödel's T in combinatory logic style
-- Andreas Abel, 2021-05-05

open import Data.Empty        using (⊥; ⊥-elim)
open import Data.Nat.Base     using (ℕ; zero; suc)
open import Data.Product      using (∃; _,_; proj₁; proj₂)

open import Relation.Nullary  using (¬_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
                              using (Star; ε; _▻_; _◅_)

-- Simple types

infixr 6 _⇒_

data Ty : Set where
  nat  : Ty
  _⇒_  : (a b : Ty) → Ty

variable
  a a' b b' c c' : Ty

-- Gödel's T in combinatory form

-- Axioms / constants

data Const : Ty → Set where
  ze   : Const nat
  su   : Const (nat ⇒ nat)
  rec  : Const (a ⇒ (nat ⇒ a ⇒ a) ⇒ nat ⇒ a)
  K    : Const (a ⇒ b ⇒ a)
  S    : Const ((a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c)

variable
  k k' : Const a

-- Proofs / terms

infixl 6 _∙_

data Tm (b : Ty) : Set where
  `_   : (k : Const b)                → Tm b
  _∙_  : (t : Tm (a ⇒ b)) (u : Tm a)  → Tm b

variable
  t t' u u' v v' w w'  : Tm a
  t₄ t₃ t₂ t₁          : Tm a

-- Weak head reduction

infix 2 _↦_

data _↦_ {a} : (t t' : Tm a) → Set where

  K     :  ` K ∙ t ∙ u                 ↦ t
  S     :  ` S ∙ t ∙ u ∙ v             ↦ t ∙ v ∙ (u ∙ v)
  ze    :  ` rec ∙ t ∙ u ∙ ` ze        ↦ t
  su    :  ` rec ∙ t ∙ u ∙ (` su ∙ v)  ↦ u ∙ v ∙ (` rec ∙ t ∙ u ∙ v)

  app   :  t ↦ t'
        →  t ∙ u ↦ t' ∙ u
  rec   :  v ↦ v'
        →  ` rec ∙ t ∙ u ∙ v ↦ ` rec ∙ t ∙ u ∙ v'

variable
  r r' : t ↦ t'

-- Multi-step weak head reduction

infix 2 _↦*_

_↦*_ : (t t' : Tm a) → Set
_↦*_ = Star _↦_

rec* : v ↦* v' → ` rec ∙ t ∙ u ∙ v ↦* ` rec ∙ t ∙ u ∙ v'
rec* ε         = ε
rec* (r ◅ rs)  = rec r ◅ rec* rs

-- Values

data Val : Tm a → Set where
  const  : Val (` k)
  K1     : Val (` K {b = b} ∙ t)
  S1     : Val (` S ∙ t)
  S2     : Val (` S ∙ t ∙ u)
  su1    : Val (` su ∙ t)
  rec1   : Val (` rec ∙ t)
  rec2   : Val (` rec ∙ t ∙ u)

-- Values are ↦-normal forms

val-nf : Val t → t ↦ t' → ⊥
val-nf const ()
val-nf S2 (app (app ()))
val-nf rec2 (app (app ()))

-- Progress

-- A term is progressive if it is either a value or has a reduct.

data Progressive (t : Tm a) : Set where
  val   : (p : Val t)   → Progressive t
  step  : (r : t ↦ t')  → Progressive t

-- rec with 3 arguments is progressive if its 3rd argument is.

progressive-rec3 : Progressive v → Progressive (` rec ∙ t ∙ u ∙ v)
progressive-rec3 (val (const {k = ze}))  = step ze
progressive-rec3 (val su1)               = step su
progressive-rec3 (step r)                = step (rec r)

-- If a function with 3 arguments is progressive, then its application to more arguments.

progressive-app3 : Progressive (t ∙ t₄ ∙ t₃ ∙ t₂) → Progressive (t ∙ t₄ ∙ t₃ ∙ t₂ ∙ t₁)
progressive-app3 (step r) = step (app r)

-- Any well-typed term is progressive.
--
-- Note that well-typedness excludes pathological cases such as (rec _ _ K).

progress : (t : Tm a) → Progressive t
progress (` k)                     = val const
progress ((` K) ∙ t₁)              = val K1
progress ((` S) ∙ t₁)              = val S1
progress ((` K) ∙ t₂ ∙ t₁)         = step K
progress ((` S) ∙ t₂ ∙ t₁)         = val S2
progress ((` su)   ∙ t₁)           = val su1
progress ((` rec) ∙ t₁)            = val rec1
progress ((` rec) ∙ t₂ ∙ t₁)       = val rec2
progress ((` rec) ∙ t₃ ∙ t₂ ∙ t₁)  = progressive-rec3 (progress _)
progress ((` K) ∙ t₃ ∙ t₂ ∙ t₁)    = step (app K)
progress ((` S) ∙ t₃ ∙ t₂ ∙ t₁)    = step S
progress (t ∙ t₄ ∙ t₃ ∙ t₂ ∙ t₁)   = progressive-app3 (progress (t ∙ t₄ ∙ t₃ ∙ t₂))

-- ↦-normal forms are values

nf-val : (t : Tm a) → (∀{t'} → t ↦ t' → ⊥) → Val t
nf-val t f with progress t
... | val   p = p
... | step  r = ⊥-elim (f r)

-- Standard model (interpreter)

-- Type interpretation

⟦_⟧ : Ty → Set
⟦ nat ⟧    =  ℕ
⟦ a ⇒ b ⟧  =  ⟦ a ⟧ → ⟦ b ⟧

variable
  n n'            : ℕ
  A A' B B' C C'  : Set
  x x'            : ⟦ a ⟧
  f f'            : ⟦ a ⇒ b ⟧

recℕ : A → (ℕ → A → A) → ℕ → A
recℕ z s zero     =  z
recℕ z s (suc n)  =  s n (recℕ z s n)

-- Interpretation of the constants

⦅_⦆ᵏ : Const a → ⟦ a ⟧
⦅ ze ⦆ᵏ       = 0
⦅ su ⦆ᵏ       = suc
⦅ rec ⦆ᵏ      = recℕ
⦅ K ⦆ᵏ x y    = x
⦅ S ⦆ᵏ x y z  = x z (y z)

-- Term interpretation

⦅_⦆ : Tm a → ⟦ a ⟧
⦅ ` k ⦆    =  ⦅ k ⦆ᵏ
⦅ t ∙ u ⦆  =  ⦅ t ⦆ ⦅ u ⦆

LR : Ty → Set₁
LR a = Tm a → ⟦ a ⟧ → Set

data ℕ∋_®_ (t : Tm nat) :  ℕ → Set where
  ze  : (rs : t ↦* ` ze)                       → ℕ∋ t ® zero
  su  : (rs : t ↦* ` su ∙ u) (⟪u⟫ : ℕ∋ u ® n)  → ℕ∋ t ® suc n

-- Logical relation between terms and objects

infix 1 _∋_®_

_∋_®_ : ∀ a → Tm a → ⟦ a ⟧ → Set
nat    ∋ t ® n  = ℕ∋ t ® n
a ⇒ b  ∋ t ® f  = ∀{u x} (⟪u⟫ : a ∋ u ® x) → b ∋ t ∙ u ® f x

-- Expansion closure

closed : t ↦ t' → a ∋ t' ® x → a ∋ t ® x
closed {a = nat}    r  (ze rs)      =  ze (r ◅ rs)
closed {a = nat}    r  (su rs ⟪t⟫)  =  su (r ◅ rs) ⟪t⟫
closed {a = a ⇒ b}  r  ⟪t⟫ ⟪u⟫      =  closed (app r) (⟪t⟫ ⟪u⟫)

closed* : t ↦* t' → a ∋ t' ® x → a ∋ t ® x
closed* ε         ⟪t⟫ = ⟪t⟫
closed* (r ◅ rs)  ⟪t⟫ = closed r (closed* rs ⟪t⟫)

-- Fundamental theorem of logical relations

-- The constants are sound

⟪_⟫ᵏ : (k : Const a) → a ∋ ` k ® ⦅ k ⦆ᵏ
⟪ ze ⟫ᵏ                        = ze ε
⟪ su ⟫ᵏ   ⟪u⟫                  = su ε ⟪u⟫
⟪ rec ⟫ᵏ  ⟪z⟫ ⟪s⟫ (ze rs)      = closed* (rec* rs) (closed ze ⟪z⟫)
⟪ rec ⟫ᵏ  ⟪z⟫ ⟪s⟫ (su rs ⟪n⟫)  = closed* (rec* rs) (closed su (⟪s⟫ ⟪n⟫ (⟪ rec ⟫ᵏ ⟪z⟫ ⟪s⟫ ⟪n⟫)))
⟪ K ⟫ᵏ    ⟪t⟫ ⟪u⟫              = closed K ⟪t⟫
⟪ S ⟫ᵏ    ⟪t⟫ ⟪u⟫ ⟪v⟫          = closed S (⟪t⟫ ⟪v⟫ (⟪u⟫ ⟪v⟫))

-- All terms are sound

⟪_⟫ : (t : Tm a) → a ∋ t ® ⦅ t ⦆
⟪ ` k   ⟫  =  ⟪ k ⟫ᵏ
⟪ t ∙ u ⟫  =  ⟪ t ⟫ ⟪ u ⟫

-- Numerals ("reification")

⌜_⌝ : ℕ → Tm nat
⌜ zero ⌝   = ` ze
⌜ suc n ⌝  = ` su ∙ ⌜ n ⌝

-- Standard reduction for naturals

infix 2 _↦s_

data _↦s_ : (t t' : Tm nat) → Set where
  ze   :                                ` ze ↦s ` ze
  su   :              (ss : t ↦s t') →  ` su ∙ t ↦s ` su ∙ t'
  _◅_  : (r : t ↦ u)  (ss : u ↦s v)  →  t ↦s v

-- Prepending a standard reduction with weak head steps

_◅◅s_ : t ↦* u → u ↦s v → t ↦s v
ε         ◅◅s ss = ss
(r ◅ rs)  ◅◅s ss = r ◅ (rs ◅◅s ss)

-- Unwinding sound naturals

unwind : (⟪t⟫ : ℕ∋ t ® n) → t ↦s ⌜ n ⌝
unwind (ze rs)      = rs ◅◅s ze
unwind (su rs ⟪t⟫)  = rs ◅◅s su (unwind ⟪t⟫)

-- Canonicity / soundness of the interpreter

canon : (t : Tm nat) → t ↦s ⌜ ⦅ t ⦆ ⌝
canon t = unwind ⟪ t ⟫

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
