module STLC where

open import Function hiding (id; _∘_)
open import Data.List hiding ([_]; lookup)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Relation.Unary.Any as Any hiding (here; lookup)
open import Relation.Binary.PropositionalEquality hiding ([_])

infixl 10 _`,_
infixl 10 _`,,_
infixr 10 _⇒_
infixr 13 `∀_﹒_ -- C-x 8 RET SMALL FULL STOP
infixr 13 `∃_﹒_ -- dito
infixr 13 _`⇒_
infixr 13 _`⇔_
infixr 14 _`∨_
infixr 15 _`∧_
infixr 16 `∀_
infixr 16 `∃_
infixr 16 `¬_
infixr 17 _`=_
infixr 18 `λ_
infixr 18 `λ_﹒_ -- dito
infixl 19 _·_
infixl 20 _[_/0]
infixl 20 _𝕡

-----------------------------------
-- Stdlib extras
-----------------------------------

pattern here     = Any.here refl
pattern _`,_ Γ a = a ∷ Γ

⊆-drop : ∀ {A : Set} {xs : List A} {x} → xs ⊆ xs `, x
⊆-drop here      = there here
⊆-drop (there p) = there (⊆-drop p)

⊆-keep : ∀ {A : Set} {xs ys : List A} {x} → xs ⊆ ys → xs `, x ⊆ ys `, x
⊆-keep _     here      = here
⊆-keep xs⊆ys (there p) = there (xs⊆ys p)

-----------------------------------
-- Language (STLC with two base types and two constants)
-----------------------------------

data Ty : Set where
  𝕓   : Ty -- individuals
  Ω   : Ty -- truth values
  _⇒_ : (a b : Ty) → Ty

variable
  a b c : Ty

ι = 𝕓
⋆ = Ω

Ctx = List Ty

variable
  Γ Γ' Γ'' : Ctx
  Δ Δ' Δ'' : Ctx
  Θ Θ' Θ'' : Ctx

_`,,_ = flip (_++_ {A = Ty})

data Tm : Ctx → Ty → Set

Form = λ Γ → Tm Γ ⋆

data Tm where
  var  : (x : a ∈ Γ) → Tm Γ a
  lam  : (t : Tm (Γ `, a) b) → Tm Γ (a ⇒ b)
  app  : (t : Tm Γ (a ⇒ b)) → (u : Tm Γ a) → Tm Γ b

  eq   : (t u : Tm Γ a) → Tm Γ ⋆
  iota : (t : Form (Γ `, a)) → Tm Γ a

variable
  t u v : Tm Γ a
  ψ ϕ φ : Form Γ

`_ : (x : a ∈ Γ) → Tm Γ a
`_ = var

`λ_ : (t : Tm (Γ `, a) b) → Tm Γ (a ⇒ b)
`λ_ = lam

`λ_﹒_ : (a : Ty) → (t : Tm (Γ `, a) b) → Tm Γ (a ⇒ b)
`λ_﹒_ _ = `λ_

_·_ : (t : Tm Γ (a ⇒ b)) → (u : Tm Γ a) → Tm Γ b
_·_ = app

_`=_ : (t u : Tm Γ a) → Form Γ
_`=_ = eq

-----------------------------------
-- Short-hands
-----------------------------------

b0 : a ∈ Γ `, a
b0 = here 

b1 : a ∈ Γ `, a `, b
b1 = there b0

b2 : a ∈ Γ `, a `, b `, c
b2 = there b1

v0 : Tm (Γ `, a) a
v0 = var b0

v1 : Tm (Γ `, a `, b) a
v1 = var b1

v2 : Tm (Γ `, a `, b `, c) a
v2 = var b2

-----------------------------------
-- Renaming/weakening and substitution
-----------------------------------

wk-var : Γ ⊆ Γ' → a ∈ Γ → a ∈ Γ'
wk-var Γ⊆Γ' x = Γ⊆Γ' x

wk : Γ ⊆ Γ' → Tm Γ a → Tm Γ' a
wk Γ⊆Γ' (var x)   = var (wk-var Γ⊆Γ' x)
wk Γ⊆Γ' (lam t)   = lam (wk (⊆-keep Γ⊆Γ') t)
wk Γ⊆Γ' (app t u) = app (wk Γ⊆Γ' t) (wk Γ⊆Γ' u)
wk Γ⊆Γ' (eq t u)  = eq (wk Γ⊆Γ' t) (wk Γ⊆Γ' u)
wk Γ⊆Γ' (iota t)  = iota (wk (⊆-keep Γ⊆Γ') t)

record Sub (Δ Γ : Ctx) : Set where
  field
    lookup : ∀ {a : Ty} → a ∈ Γ → Tm Δ a
open Sub

variable
  σ τ : Sub Δ Γ

wk-sub : Δ ⊆ Δ' → Sub Δ Γ → Sub Δ' Γ
wk-sub Δ⊆Δ' σ .lookup x = wk Δ⊆Δ' (σ .lookup x)

Sub-refl : Sub Γ Γ
Sub-refl .lookup = var

id = Sub-refl

⟨_,_⟩ : Sub Δ Γ → Tm Δ a → Sub Δ (Γ `, a)
⟨_,_⟩ σ t .lookup here      = t
⟨_,_⟩ σ t .lookup (there p) = σ .lookup p

Sub-drop : Sub (Γ `, a) Γ
Sub-drop .lookup x = var (there x) -- ≡ wk-sub ⊆-drop Sub-refl

[_] : (t : Tm Γ a) → Sub Γ (Γ `, a)
[_] t = ⟨ Sub-refl , t ⟩

Sub-keep : Sub Δ Γ → Sub (Δ `, a) (Γ `, a)
Sub-keep σ = ⟨ wk-sub ⊆-drop σ , v0 ⟩

⟨_⟩ = Sub-keep

sub : Sub Δ Γ → Tm Γ a → Tm Δ a
sub σ (var x)   = σ .lookup x
sub σ (lam t)   = lam (sub (Sub-keep σ) t)
sub σ (app t u) = app (sub σ t) (sub σ u)
sub σ (eq t u)  = eq (sub σ t) (sub σ u)
sub σ (iota t)  = iota (sub (Sub-keep σ) t)

Sub-trans : Sub Θ Δ → Sub Δ Γ → Sub Θ Γ
Sub-trans τ σ .lookup x = sub τ (σ .lookup x)

_∘_ : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
_∘_ σ τ = Sub-trans τ σ

_ : Sub-trans ⟨ σ , t ⟩ Sub-drop ≡ σ
_ = refl

_[_/0] : Tm (Γ `, a) b → Tm Γ a → Tm Γ b
t [ u /0] = sub [ u ] t

_𝕡 : Tm Γ a → Tm (Γ `, b) a
_𝕡 = sub Sub-drop

postulate
  sub-refl  : ∀ (t : Tm Γ a) → sub Sub-refl t ≡ t
  sub-trans : ∀ (τ : Sub Θ Δ) (σ : Sub Δ Γ) (t : Tm Γ a) → sub τ (sub σ t) ≡ sub (Sub-trans τ σ) t

-----------------------------------
-- Syntactic sugar/derived operations
-----------------------------------

`⊤ : Form Γ
`⊤ = `λ ⋆ ﹒ v0 `= `λ ⋆ ﹒ v0

`⊥ : Form Γ
`⊥ = `λ ⋆ ﹒ `⊤ `= `λ ⋆ ﹒ v0

`¬_ : Form Γ → Form Γ
`¬ t = t `= `⊥

undefined : Tm Γ a
undefined = iota (`¬ v0 `= v0)

_`∧_ : (φ ψ : Form Γ) → Form Γ
t `∧ u = `λ ⋆ ⇒ ⋆ ⇒ ⋆ ﹒ v0 · `⊤ · `⊤ `= `λ ⋆ ⇒ ⋆ ⇒ ⋆ ﹒ v0 · t 𝕡 · u 𝕡

_`∨_ : (φ ψ : Form Γ) → Form Γ
t `∨ u = `¬ (`¬ t `∧ `¬ u)

_`⇒_ : (φ ψ : Form Γ) → Form Γ
t `⇒ u = `¬ t `∨ u

_`⇔_ : (φ ψ : Form Γ) → Form Γ
t `⇔ u = t `= u

`∀_ : (φ : Form (Γ `, a)) → Form Γ
`∀_ t = `λ t `= `λ `⊤

`∀_﹒_ : (a : Ty) → (φ : Form (Γ `, a)) → Form Γ
`∀_﹒_ _ = `∀_

`∃_ : (φ : Form (Γ `, a)) → Form Γ
`∃_ t = `¬ `∀ `¬ t

`∃_﹒_ : (a : Ty) → (φ : Form (Γ `, a)) → Form Γ
`∃_﹒_ _ = `∃_

`∃!_ : (φ : Form (Γ `, a)) → Form Γ
`∃!_ t = `∃ (t `∧ `∀ (wk (⊆-keep ⊆-drop) t `⇒ v0 `= v1))

`∃!_﹒_ : (a : Ty) → (φ : Form (Γ `, a)) → Form Γ
`∃!_﹒_ _ = `∃!_

-----------------------------------
-- Sequents
-----------------------------------

FormCtx = λ Γ → List (Form Γ)

variable
  Ψ Φ : FormCtx Γ
