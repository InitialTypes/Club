module STLC where

open import Data.List hiding ([_])
open import Data.List.Membership.Propositional
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Relation.Unary.Any as Any hiding (here)
open import Relation.Binary.PropositionalEquality hiding ([_]; subst)

infix   8 _⊢_
infix   8  _⊨_
infixl 10 _`,_
infixl 10 _`,,_
infixr 10 _⇒_
infixr 14 `∀_
infixr 14 `∀_﹒_
infixr 14 _`=_
infixr 14 _`⇒_
infixr 14 _⇔_
infixl 15 _∨_
infixl 16 _∧_
infix  17 ¬_
infixr 18 `λ_
infixr 18 `λ_﹒_
infixl 19 _·_
infixl 20 _[_]
infixl 20 _p

pattern here     = Any.here refl
pattern _`,_ Γ a = a ∷ Γ

⊆-drop : ∀ {A : Set} {xs : List A} {x} → xs ⊆ x ∷ xs
⊆-drop here      = there here
⊆-drop (there p) = there (⊆-drop p)

⊆-keep : ∀ {A : Set} {xs ys : List A} {x} → xs ⊆ ys → x ∷ xs ⊆ x ∷ ys
⊆-keep _     here      = here
⊆-keep xs⊆ys (there p) = there (xs⊆ys p)

data Ty : Set where
  ι   : Ty -- individuals
  ⋆   : Ty -- truth values
  _⇒_ : (a b : Ty) → Ty

variable
  a b c : Ty

Ω = ⋆

Ctx = List Ty

variable
  Γ Γ' Γ'' : Ctx
  Δ Δ' Δ'' : Ctx

_`,,_ : (Γ Δ : Ctx) → Ctx
Γ `,, Δ = Δ ++ Γ

data _⊢_ (Γ : Ctx) : Ty → Set where
  var  : (x : a ∈ Γ) → Γ ⊢ a
  lam  : (t : Γ `, a ⊢ b) → Γ ⊢ a ⇒ b
  app  : (t : Γ ⊢ a ⇒ b) → (u : Γ ⊢ a) → Γ ⊢ b

  eq   : (t u : Γ ⊢ a) → Γ ⊢ ⋆
  iota : (t : Γ `, a ⊢ ⋆) → Γ ⊢ a

variable
  t u : Γ ⊢ a

b0 : a ∈ Γ `, a
b0 = here 

b1 : a ∈ Γ `, a `, b
b1 = there b0

b2 : a ∈ Γ `, a `, b `, c
b2 = there b1

v0 : Γ `, a ⊢ a
v0 = var b0

v1 : Γ `, a `, b ⊢ a
v1 = var b1

v2 : Γ `, a `, b `, c ⊢ a
v2 = var b2

`_ : (x : a ∈ Γ) → Γ ⊢ a
`_ = var

`λ_ : (t : Γ `, a ⊢ b) → Γ ⊢ a ⇒ b
`λ_ = lam

`λ_﹒_ : (a : Ty) → (t : Γ `, a ⊢ b) → Γ ⊢ a ⇒ b
`λ_﹒_ _ = lam

_·_ : (t : Γ ⊢ a ⇒ b) → (u : Γ ⊢ a) → Γ ⊢ b
_·_ = app

_`=_ : (t u : Γ ⊢ a) → Γ ⊢ ⋆
_`=_ = eq

wk : Γ ⊆ Γ' → Γ ⊢ a → Γ' ⊢ a
wk Γ⊆Γ' (var x)   = var (Γ⊆Γ' x)
wk Γ⊆Γ' (lam t)   = lam (wk (⊆-keep Γ⊆Γ') t)
wk Γ⊆Γ' (app t u) = app (wk Γ⊆Γ' t) (wk Γ⊆Γ' u)
wk Γ⊆Γ' (eq t u)  = eq (wk Γ⊆Γ' t) (wk Γ⊆Γ' u)
wk Γ⊆Γ' (iota t)  = iota (wk (⊆-keep Γ⊆Γ') t)

_⊨_ : Ctx → Ctx → Set
Δ ⊨ Γ = ∀ {a : Ty} → a ∈ Γ → Δ ⊢ a

⊨-refl : Γ ⊨ Γ
⊨-refl = var

⊨-keep : Γ ⊨ Δ → Γ `, a ⊨ Δ `, a
⊨-keep x here      = var here
⊨-keep x (there p) = wk ⊆-drop (x p)

⊨-drop : Γ ⊢ a → Γ ⊨ Γ `, a
⊨-drop t here      = t
⊨-drop t (there x) = var x

subst : Δ ⊨ Γ → Γ ⊢ a → Δ ⊢ a
subst σ (var x)   = σ x
subst σ (lam t)   = lam (subst (⊨-keep σ) t)
subst σ (app t u) = app (subst σ t) (subst σ u)
subst σ (eq t u)  = eq (subst σ t) (subst σ u)
subst σ (iota t)  = iota (subst (⊨-keep σ) t)

_[_] : Γ `, a ⊢ b → Γ ⊢ a → Γ ⊢ b
t [ u ] = subst (⊨-drop u) t

_p : Γ ⊢ a → Γ `, b ⊢ a
_p = wk ⊆-drop

T : Γ ⊢ ⋆
T = `λ ⋆ ﹒ v0 `= `λ ⋆ ﹒ v0

F : Γ ⊢ ⋆
F = `λ ⋆ ﹒ T `= `λ ⋆ ﹒ v0

¬_ : Γ ⊢ ⋆ → Γ ⊢ ⋆
¬ t = t `= F

_∧_ : Γ ⊢ ⋆ → Γ ⊢ ⋆ → Γ ⊢ ⋆
t ∧ u = `λ ⋆ ⇒ ⋆ ⇒ ⋆ ﹒ v0 · T · T `= `λ ⋆ ⇒ ⋆ ⇒ ⋆ ﹒ v0 · t p · u p

_∨_ : Γ ⊢ ⋆ → Γ ⊢ ⋆ → Γ ⊢ ⋆
t ∨ u = ¬ (¬ t ∧ ¬ u)

_`⇒_ : Γ ⊢ ⋆ → Γ ⊢ ⋆ → Γ ⊢ ⋆
t `⇒ u = ¬ t ∨ u

_⇔_ : Γ ⊢ ⋆ → Γ ⊢ ⋆ → Γ ⊢ ⋆
t ⇔ u = t `= u

`∀_ : Γ `, a ⊢ ⋆ → Γ ⊢ ⋆
`∀_ t = `λ t `= `λ T

`∀_﹒_ : (a : Ty) → Γ `, a ⊢ ⋆ → Γ ⊢ ⋆
`∀_﹒_ _ = `∀_

Form : Ctx → Set
Form Γ = Γ ⊢ ⋆

variable
  Ψ Φ   : List (Form Γ)
  ψ ϕ φ : Form Γ

FormCtx = λ Γ → List (Form Γ)
