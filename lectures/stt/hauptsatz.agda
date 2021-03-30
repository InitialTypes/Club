open import Data.List hiding ([_])
open import Data.List.Membership.Propositional 
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Relation.Unary.Any as Any hiding (here)
open import Relation.Binary.PropositionalEquality hiding ([_]; subst) 
open import Data.Sum

⊆-drop : ∀ {A : Set} (xs : List A) x → xs ⊆ x ∷ xs
⊆-drop .(_ ∷ _) x (Any.here px) = there (Any.here px)
⊆-drop .(_ ∷ _) x (there p) = there (⊆-drop _ _ p)

⊆-keep : ∀ {A : Set} {xs ys : List A} x → xs ⊆ ys → x ∷ xs ⊆ x ∷ ys
⊆-keep x x₁ (Any.here px) = Any.here px
⊆-keep x x₁ (there x₂) = there (x₁ x₂)

infix   8 _⊢_
infix   8 _⊩_
infixl  9 _[_]
infixr  9 _⊆_
infixl 10 _`,_
infixl 10 _`,,_
infixr 9  _⊨_
infixr 10 _⇒_
infixr 15 `∀_
infixr 15 `∀[_]_
infixr 15 `∀_﹒_
infixr 15 _`⇒_
infixr 15 _⇔_
infixl 16 _∨_
infixl 17 _∧_
infix  18 ¬_
infixl 19 _p

data Ty : Set where
  ι   : Ty -- individuals
  ⋆   : Ty -- truth values
  _⇒_ : (a b : Ty) → Ty

variable
  a b c : Ty

Ctx = List Ty

variable
  Γ Γ' Γ'' : Ctx
  Δ Δ' Δ'' : Ctx

pattern here     = Any.here refl
pattern _`,_ Γ a = a ∷ Γ

_s : Ty → Ctx
a s = [] `, a

_`,,_ : (Γ Δ : Ctx) → Ctx
Γ `,, Δ = Δ ++ Γ

data _⊢_ (Γ : Ctx) : Ty → Set where
  var  : a ∈ Γ → Γ ⊢ a 
  lam  : Γ `, a ⊢ b → Γ ⊢ a ⇒ b
  app  : Γ ⊢ a ⇒ b → Γ ⊢ a → Γ ⊢ b

  eq   : Γ ⊢ a → Γ ⊢ a → Γ ⊢ ⋆
  iota : Γ `, a ⊢ ⋆ → Γ ⊢ a 

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

lam[_]_ : (a : Ty) → Γ `, a ⊢ b → Γ ⊢ a ⇒ b
lam[_]_ _ = lam

wk : Γ ⊆ Γ' → Γ ⊢ a → Γ' ⊢ a
wk Γ⊆Γ' (var x)    = var (Γ⊆Γ' x)
wk Γ⊆Γ' (lam t)    = lam (wk (⊆-keep _ Γ⊆Γ') t)
wk Γ⊆Γ' (app t t₁) = app (wk Γ⊆Γ' t) (wk Γ⊆Γ' t₁)
wk Γ⊆Γ' (eq t t₁)  = eq (wk Γ⊆Γ' t₁) (wk Γ⊆Γ' t₁)
wk Γ⊆Γ' (iota t)   = iota (wk (⊆-keep _ Γ⊆Γ') t)

_⊨_ : Ctx → Ctx → Set
Δ ⊨ Γ = ∀ (a : Ty) → a ∈ Γ → Δ ⊢ a 

⊨-refl : Γ ⊨ Γ
⊨-refl _ = var

⊨-keep : Γ ⊨ Δ → Γ `, a ⊨ Δ `, a
⊨-keep x a (Any.here px) = var (Any.here px)
⊨-keep x a (there p) = wk (⊆-drop _ _) (x _ p)

⊨-drop : Γ ⊢ a → Γ ⊨ Γ `, a
⊨-drop t a here      = t
⊨-drop t a (there x) = var x

subst : Δ ⊨ Γ → Γ ⊢ a → Δ ⊢ a
subst σ (var x)    = σ _ x
subst σ (lam t)    = lam (subst (⊨-keep σ) t)
subst σ (app t t₁) = app (subst σ t) (subst σ t₁)
subst σ (eq t t₁)  = eq (subst σ t₁) (subst σ t₁)
subst σ (iota t)   = iota (subst (⊨-keep σ) t)

_[_] : Γ `, a ⊢ b → Γ ⊢ a → Γ ⊢ b
t [ u ] = subst (⊨-drop u) t

_p : Γ ⊢ a → Γ `, b ⊢ a
_p = wk (⊆-drop _ _)

T : Γ ⊢ ⋆
T = eq (lam[ ⋆ ] v0) (lam[ ⋆ ] v0)

F : Γ ⊢ ⋆
F = eq (lam[ ⋆ ] T) (lam[ ⋆ ] v0)

¬_ : Γ ⊢ ⋆ → Γ ⊢ ⋆
¬ t = eq t F

_∧_ : Γ ⊢ ⋆ → Γ ⊢ ⋆ → Γ ⊢ ⋆
t ∧ u = eq (lam[ ⋆ ⇒ ⋆ ⇒ ⋆ ] (app (app v0 T) T))
           (lam[ ⋆ ⇒ ⋆ ⇒ ⋆ ] (app (app v0 (t p)) (u p))) 

_∨_ : Γ ⊢ ⋆ → Γ ⊢ ⋆ → Γ ⊢ ⋆
t ∨ u = ¬ (¬ t ∧ ¬ u)

_`⇒_ : Γ ⊢ ⋆ → Γ ⊢ ⋆ → Γ ⊢ ⋆
t `⇒ u = ¬ t ∨ u

_⇔_ : Γ ⊢ ⋆ → Γ ⊢ ⋆ → Γ ⊢ ⋆
t ⇔ u = eq t u

`∀_ : Γ `, a ⊢ ⋆ → Γ ⊢ ⋆
`∀_ t = eq (lam t) (lam T)

`∀[_]_ : (a : Ty) → Γ `, a ⊢ ⋆ → Γ ⊢ ⋆
`∀[_]_ _ = `∀_

`∀_﹒_ : (a : Ty) → Γ `, a ⊢ ⋆ → Γ ⊢ ⋆
`∀_﹒_ _ = `∀_

Form : Ctx → Set
Form Γ = Γ ⊢ ⋆ 

variable
  Φ : List (Form Γ)
  ψ ϕ φ : Form Γ

data _⊩_ (Φ : List (Form Γ)) : Form Γ → Set where
  Ass : t ∈ Φ → Φ ⊩ t

  R : (ψ : Form (Γ `, a)) → Φ ⊩ eq t u → Φ ⊩ ψ [ t ]
    --------------------------------------------------
    →                  Φ ⊩ ψ [ u ]

  A1 : Φ ⊩ `∀ ⋆ ⇒ ⋆ ﹒ app v0 T ∧ app v0 F ⇔ `∀ ⋆ ﹒ app v1 v0

  A2 : Φ ⊩ `∀ a ﹒ `∀ a ﹒ eq v1 v0 `⇒ `∀ a ⇒ ⋆ ﹒ app v0 v2 ⇔ app v0 v1

  A3 : Φ ⊩ `∀ a ⇒ b ﹒ `∀ a ⇒ b ﹒ eq v1 v0 ⇔ `∀ a ﹒ eq (app v2 v0) (app v1 v0)

  A4 : {t : Γ `, a ⊢ b} {u : Γ ⊢ a} → Φ ⊩ eq (app (lam t) u) (t [ u ]) 

T-true : Φ ⊩ T
T-true = R (eq v0 (lam[ ⋆ ] v0))
           (A4 {t = v0} {u = lam[ ⋆ ] v0})
           {!A4!}

-- truth-lemma : Φ ⊩ eq ψ T → Φ ⊩ ψ 
-- truth-lemma = {!!}

-- `∀E :  Φ ⊩ `∀ ψ → Φ ⊩ ψ [ t ]
-- `∀E p = {!!}

-- ∧E₁ :  Φ ⊩ φ ∧ ψ → Φ ⊩ φ
-- ∧E₁ p = {!!}

-- LEM : Φ ⊩ φ ∨ ¬ φ
-- LEM = {!!}

-- I : Φ ⊩ φ `⇒ φ
-- I = {!!}

-- eq-refl : ∀ (t : Γ ⊢ a) → Φ ⊩ eq t t
-- eq-refl t = {!!}

-- eq-sym : ∀ (t u : Γ ⊢ a) → Φ ⊩ eq t u → _ -- Φ ⊩ eq u t 
-- eq-sym t u r = R (eq v0 (u p)) r {!!}

-- eq-trans : ∀ (t u w : Γ ⊢ a) →
--          Φ ⊩ eq t u → Φ ⊩ eq u w → _ -- Φ ⊩ eq ϕ φ
-- eq-trans t u w r q = R (eq (u p) v0) q {!!}
