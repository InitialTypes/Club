module STLC where

open import Data.List hiding ([_])
open import Data.List.Membership.Propositional
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Relation.Unary.Any as Any hiding (here)
open import Relation.Binary.PropositionalEquality hiding ([_])

infix   8 _⊢_
infix   8  _⊨_
infixl 10 _`,_
infixl 10 _`,,_
infixr 10 _⇒_
infixr 13 `∀_﹒_
infixr 13 `∃_﹒_
infixr 13 _`⇒_
infixr 13 _⇔_
infixr 14 _∨_
infixr 15 _∧_
infixr 16 `∀_
infixr 16 `∃_
infixr 16 ¬_
infixr 17 _`=_
infixr 18 `λ_
infixr 18 `λ_﹒_
infixl 19 _·_
infixl 20 _[_/0]
infixl 20 _𝕡

-----------------------------------
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
-----------------------------------

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
  Θ Θ' Θ'' : Ctx

_`,,_ : (Γ Δ : Ctx) → Ctx
Γ `,, Δ = Δ ++ Γ

data _⊢_ (Γ : Ctx) : Ty → Set where
  var  : (x : a ∈ Γ) → Γ ⊢ a
  lam  : (t : Γ `, a ⊢ b) → Γ ⊢ a ⇒ b
  app  : (t : Γ ⊢ a ⇒ b) → (u : Γ ⊢ a) → Γ ⊢ b

  eq   : (t u : Γ ⊢ a) → Γ ⊢ ⋆
  iota : (t : Γ `, a ⊢ ⋆) → Γ ⊢ a

-----------------------------------
-----------------------------------

variable
  t u v : Γ ⊢ a

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

-----------------------------------
-----------------------------------

wk : Γ ⊆ Γ' → Γ ⊢ a → Γ' ⊢ a
wk Γ⊆Γ' (var x)   = var (Γ⊆Γ' x)
wk Γ⊆Γ' (lam t)   = lam (wk (⊆-keep Γ⊆Γ') t)
wk Γ⊆Γ' (app t u) = app (wk Γ⊆Γ' t) (wk Γ⊆Γ' u)
wk Γ⊆Γ' (eq t u)  = eq (wk Γ⊆Γ' t) (wk Γ⊆Γ' u)
wk Γ⊆Γ' (iota t)  = iota (wk (⊆-keep Γ⊆Γ') t)

-- record _⊨_ (Δ Γ : Ctx) : Set where
--   field
--     Sub : ∀ {a : Ty} → a ∈ Γ → Δ ⊢ a
-- open _⊨_

_⊨_ : (Δ Γ : Ctx) → Set
_⊨_ Δ Γ = ∀ {a : Ty} → a ∈ Γ → Δ ⊢ a

variable
  σ τ : Δ ⊨ Γ

wk-sub : Δ ⊆ Δ' → Δ ⊨ Γ → Δ' ⊨ Γ
-- wk-sub Δ⊆Δ' σ .Sub x = wk Δ⊆Δ' (σ .Sub x)
wk-sub Δ⊆Δ' σ x = wk Δ⊆Δ' (σ x)

⊨-refl : Γ ⊨ Γ
-- ⊨-refl .Sub = var
⊨-refl = var

id = ⊨-refl

⟨_,_⟩ : Δ ⊨ Γ → Δ ⊢ a → Δ ⊨ Γ `, a
-- ⟨_,_⟩ σ t .Sub here      = t
-- ⟨_,_⟩ σ t .Sub (there p) = σ .Sub p
⟨_,_⟩ σ t here      = t
⟨_,_⟩ σ t (there p) = σ p

⊨-drop : Γ `, a ⊨ Γ
⊨-drop = wk-sub ⊆-drop ⊨-refl

[_] : (t : Γ ⊢ a) → Γ ⊨ Γ `, a
[_] t = ⟨ ⊨-refl , t ⟩

⊨-keep : Δ ⊨ Γ → Δ `, a ⊨ Γ `, a
⊨-keep σ = ⟨ wk-sub ⊆-drop σ , v0 ⟩

⟨_⟩ = ⊨-keep

sub : Δ ⊨ Γ → Γ ⊢ a → Δ ⊢ a
-- sub σ (var x)   = σ .Sub x
sub σ (var x)   = σ x
sub σ (lam t)   = lam (sub (⊨-keep σ) t)
sub σ (app t u) = app (sub σ t) (sub σ u)
sub σ (eq t u)  = eq (sub σ t) (sub σ u)
sub σ (iota t)  = iota (sub (⊨-keep σ) t)

⊨-trans : Θ ⊨ Δ → Δ ⊨ Γ → Θ ⊨ Γ
-- ⊨-trans τ σ .Sub x = sub τ (σ .Sub x)
⊨-trans τ σ x = sub τ (σ x)

_∘_ : Δ ⊨ Γ → Θ ⊨ Δ → Θ ⊨ Γ
_∘_ σ τ = ⊨-trans τ σ

_[_/0] : Γ `, a ⊢ b → Γ ⊢ a → Γ ⊢ b
t [ u /0] = sub [ u ] t

_𝕡 : Γ ⊢ a → Γ `, b ⊢ a
_𝕡 = sub ⊨-drop

open ≡-Reasoning

⊨-keep-trans : ∀ (τ : Θ ⊨ Δ) (σ : Δ ⊨ Γ) a → _≡_ {A = Θ `, a ⊨ Γ `, a} (⊨-keep (⊨-trans τ σ)) (⊨-trans (⊨-keep τ) (⊨-keep σ))
⊨-keep-trans {Θ} {Δ} {Γ} τ σ a = {!!}

sub-trans : ∀ (τ : Θ ⊨ Δ) (σ : Δ ⊨ Γ) (t : Γ ⊢ a) → sub (⊨-trans τ σ) t ≡ sub τ (sub σ t)
sub-trans τ σ (var x)                                                                         = refl
sub-trans τ σ (lam {a = a} t)  rewrite ⊨-keep-trans τ σ a | sub-trans (⊨-keep τ) (⊨-keep σ) t = refl
sub-trans τ σ (app t u)        rewrite sub-trans τ σ t    | sub-trans τ          σ          u = refl
sub-trans τ σ (eq t u)         rewrite sub-trans τ σ t    | sub-trans τ          σ          u = refl
sub-trans τ σ (iota {a = a} t) rewrite ⊨-keep-trans τ σ a | sub-trans (⊨-keep τ) (⊨-keep σ) t = refl

-----------------------------------
-----------------------------------

T : Γ ⊢ ⋆
T = `λ ⋆ ﹒ v0 `= `λ ⋆ ﹒ v0

F : Γ ⊢ ⋆
F = `λ ⋆ ﹒ T `= `λ ⋆ ﹒ v0

¬_ : Γ ⊢ ⋆ → Γ ⊢ ⋆
¬ t = t `= F

_∧_ : Γ ⊢ ⋆ → Γ ⊢ ⋆ → Γ ⊢ ⋆
t ∧ u = `λ ⋆ ⇒ ⋆ ⇒ ⋆ ﹒ v0 · T · T `= `λ ⋆ ⇒ ⋆ ⇒ ⋆ ﹒ v0 · t 𝕡 · u 𝕡

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

`∃_ : Γ `, a ⊢ ⋆ → Γ ⊢ ⋆
`∃_ t = ¬ (`∀ ¬ t)

`∃_﹒_ : (a : Ty) → Γ `, a ⊢ ⋆ → Γ ⊢ ⋆
`∃_﹒_ _ = `∃_

`∃!_ : Γ `, a ⊢ ⋆ → Γ ⊢ ⋆
`∃!_ t = `∃ (t ∧ `∀ (wk (⊆-keep ⊆-drop) t `⇒ v0 `= v1))

⊥ : Γ ⊢ a
⊥ = iota (¬ v0 `= v0)

-----------------------------------
-----------------------------------

Form : Ctx → Set
Form Γ = Γ ⊢ ⋆

variable
  Ψ Φ   : List (Form Γ)
  ψ ϕ φ : Form Γ

FormCtx = λ Γ → List (Form Γ)
