-- A sound call-by-name interpreter for Gödel's T
-- Andreas Abel, 2021-05-06

open import Size

open import Category.Monad           using (module RawMonad)
open import Codata.Delay             using (Delay; now; later)
open import Codata.Delay.Categorical using (module Sequential)
open import Codata.Thunk             using (Thunk; force)

open import Data.Empty        using (⊥; ⊥-elim)
open import Data.List         using (List; []; _∷_)
open import Data.Nat.Base     using (ℕ; zero; suc)
open import Data.Product      using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Unit         using (⊤)

open import Data.List.Membership.Propositional public using (_∈_)
open import Data.List.Relation.Unary.All public using (All; []; _∷_) hiding (module All)
-- open import Data.List.Relation.Binary.Pointwise public using (Pointwise; []; _∷_) hiding (module Pointwise)
open import Data.List.Relation.Unary.Any public using (here; there)

open import Function using (case_of_)

open import Relation.Nullary  using (¬_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
                              using (Star; ε; _▻_; _◅_)

open import Relation.Binary.PropositionalEquality public using (_≡_; refl)

pattern here! = here refl

module All where
  open import Data.List.Relation.Unary.All public

-- Gödel's T: STLC with natural numbers and (higher-order) primitive recursion
------------------------------------------------------------------------------

-- Simple types

infixr 6 _⇒_

data Ty : Set where
  nat  : Ty
  _⇒_  : (a b : Ty) → Ty

variable
  a a' b b' c c' : Ty

-- Contexts

Cxt = List Ty

variable
  Γ Γ' Δ Δ' : Cxt

-- Variables

variable
  x x' : a ∈ Γ

-- Terms

data Tm (Γ : Cxt) : Ty → Set where
  var : (x : a ∈ Γ) → Tm Γ a
  abs : (t : Tm (a ∷ Γ) b) → Tm Γ (a ⇒ b)
  app : (t : Tm Γ (a ⇒ b)) (u : Tm Γ a) → Tm Γ b
  ze  : Tm Γ nat
  su  : (t : Tm Γ nat) → Tm Γ nat
  rec : (t : Tm Γ a) (u : Tm (a ∷ nat ∷ Γ) a) (v : Tm Γ nat) → Tm Γ a

-- Standard semantics

⟦_⟧ : Ty → Set
⟦ nat ⟧    =  ℕ
⟦ a ⇒ b ⟧  =  ⟦ a ⟧ → ⟦ b ⟧

G⟦_⟧ : Cxt → Set
G⟦_⟧ = All ⟦_⟧

variable
  n n'            : ℕ
  A A' B B' C C'  : Set
  f f'            : ⟦ a ⇒ b ⟧
  g g' gz gs gn   : ⟦ a ⟧
  ρ ρ'            : G⟦ Γ ⟧

recℕ : A → (ℕ → A → A) → ℕ → A
recℕ z s zero     =  z
recℕ z s (suc n)  =  s n (recℕ z s n)


⦅_⦆ : Tm Γ a → G⟦ Γ ⟧ → ⟦ a ⟧
⦅ var x ⦆     ρ    = All.lookup ρ x
⦅ abs t ⦆     ρ d  = ⦅ t ⦆ (d ∷ ρ)
⦅ app t u ⦆   ρ    = ⦅ t ⦆ ρ (⦅ u ⦆ ρ)
⦅ ze ⦆        ρ    = zero
⦅ su t ⦆      ρ    = suc (⦅ t ⦆ ρ)
⦅ rec z s t ⦆ ρ    = recℕ (⦅ z ⦆ ρ) (λ n d → ⦅ s ⦆ (d ∷ n ∷ ρ)) (⦅ t ⦆ ρ)


-- Environment and closures

mutual
  Env : (Γ : Cxt) → Set
  Env = All Clos

  record Clos (a : Ty) : Set where
    inductive; constructor clos
    field
      {cxt} : Cxt
      tm    : Tm cxt a
      env   : Env cxt
  -- TODO: add a special closure for rec here

variable
  γ γ' δ δ' : Env Γ
  cl cl' clf clg cln cls clz : Clos a

-- CBN values

data Val : Ty → Set where
  abs :  (t : Tm (a ∷ Δ) b) (δ : Env Δ) → Val (a ⇒ b)
  ze  : Val nat
  su  : (cl : Clos nat) → Val nat

variable
  v w : Val a

-- Call-by-name interpreter

-- infix 2 _↘_

variable
  i      : Size
  d d'   : Delay A i
  F      : Size → Set
  th th' : Thunk F i

-- Delayed value (partiality by a priori potential non-termination)

DVal : Ty → Size → Set
DVal a = Delay (Val a)

-- Delayed closure

DClos : Ty → Size → Set
DClos a = Delay (Clos a)

-- Interpreter in the delay monad

mutual

  -- Evaluate terms in an environment

  eval : Tm Γ a → Env Γ → DVal a i
  eval (var x) γ       = later (evalCl' (All.lookup γ x))
  eval (abs t) γ       = now (abs t γ)
  eval (app t u) γ     = apply (eval t γ) (clos u γ)

  eval ze γ            = now ze
  eval (su t) γ        = now (su (clos t γ))
  eval (rec z s t) γ   =
    eval t γ >>= λ where
      ze       → eval z γ
      (su cl)  → eval s (clos (rec z s t) γ ∷ cl ∷ γ)
    where open RawMonad Sequential.monad

  -- Call-by-name application

  apply : DVal (a ⇒ b) i → Clos a → DVal b i
  apply f cl = do
    abs t γ ← f
    later (eval' t (cl ∷ γ))
    where open RawMonad Sequential.monad

  eval' : Tm Γ a → Env Γ → Thunk (DVal a) i
  eval' t γ .force = eval t γ

  -- Evaluate closures

  evalCl : Clos a → DVal a i
  evalCl (clos t γ) = eval t γ

  evalCl' : Clos a → Thunk (DVal a) i
  evalCl' (clos t γ) = eval' t γ

-- Termination of delayed result

module _ {ℓ} {A : Set ℓ} where

 infix 3 _⇓_
 data _⇓_ : Delay A ∞ → A → Set ℓ where
   now   : ∀ {a}                   → now a   ⇓ a
   later : ∀ {d a} → d .force ⇓ a  → later d ⇓ a

variable
  r r' : d ⇓ _

-- Logical relation

-- Base case: terminate with lazy natural number

data ℕ∋_®_ (d : DVal nat ∞) :  ℕ → Set where
  ze  : (r : d ⇓ ze)                              → ℕ∋ d ® zero
  su  : (r : d ⇓ su cl) (⟪n⟫ : ℕ∋ evalCl cl ® n)  → ℕ∋ d ® suc n

-- Logical relation by induction on types

infix 1 _∋_®_ _∋_©_

mutual

  _∋_©_ : ∀ a → Clos a → ⟦ a ⟧ → Set
  a ∋ cl © g = a ∋ evalCl cl ® g

  _∋_®_ : ∀ a → DVal a ∞ → ⟦ a ⟧ → Set
  nat    ∋ d ® n  = ℕ∋ d ® n
  a ⇒ b  ∋ d ® f  = ∀{cl g} (⟪u⟫ : a ∋ cl © g) → b ∋ apply d cl ® f g

-- Expansion property of LR

laterℕ : ℕ∋ th .force ® n →  ℕ∋ later th ® n
laterℕ (ze r)     = ze (later r)
laterℕ (su r ⟪n⟫) = su (later r) ⟪n⟫

laterR : a ∋ th .force ® g →  a ∋ later th ® g
laterR {a = nat}   ⟪n⟫     = laterℕ ⟪n⟫
laterR {a = a ⇒ b} ⟪t⟫ ⟪u⟫ = laterR {a = b} (⟪t⟫ ⟪u⟫)

-- Logical relation extended pointwise to environments

infix 1 _∋G_®_

_∋G_®_ : ∀ Γ → Env Γ → G⟦ Γ ⟧ → Set
[]       ∋G  _         ®  _        =  ⊤
(a ∷ Γ)  ∋G  (cl ∷ γ)  ®  (g ∷ ρ)  =  (a ∋ cl © g) × (Γ ∋G γ ® ρ)

-- Looking up a variable in the environment LR

lookupG :  Γ ∋G γ ® ρ → (x : a ∈ Γ) → a ∋ All.lookup γ x © All.lookup ρ x
lookupG {γ = cl ∷ _} {ρ = g ∷ _} (⟪cl⟫ , ⟪γ⟫) here!   = ⟪cl⟫
lookupG {γ = cl ∷ _} {ρ = g ∷ _} (⟪cl⟫ , ⟪γ⟫) (there x) = lookupG ⟪γ⟫ x

-- LR version of recursor (WIP)

⟪rec⟫ : (z : Tm Γ a)
        (⟪z⟫ : a ∋ clos z γ © gz)
        (s : Tm (a ∷ nat ∷ Γ) a)
        (⟪s⟫ : ∀{cln n clg g} → nat ∋ cln © n → a ∋ clg © g → a ∋ clos s (clg ∷ cln ∷ γ) © gs n g)
        -- (⟪s⟫ : ∀{cln n clg g} → nat ∋ cln © n → a ∋ clg © g → a ∋ apply (apply cls cln) clg ® gs n g)
        (t : Tm Γ nat)
        (⟪t⟫ : nat ∋ clos t γ © n)
        -- (⟪t⟫ : ℕ∋ d ® n)
      → a ∋ clos (rec z s t) γ © recℕ gz gs n
⟪rec⟫ {γ = γ} z ⟪z⟫ s ⟪s⟫ t ⟪t⟫ with eval t γ
⟪rec⟫ {γ = γ} z ⟪z⟫ s ⟪s⟫ t (ze r)     | now ze      = ⟪z⟫
⟪rec⟫ {γ = γ} z ⟪z⟫ s ⟪s⟫ t (su r ⟪t⟫) | now (su (clos t' δ)) = ⟪s⟫ {!⟪t⟫!} (⟪rec⟫ {γ = γ} z ⟪z⟫ s ⟪s⟫ {!!} {!⟪t⟫!})
... | later d = laterR {!!}
-- ⟪rec⟫ z ⟪z⟫ s ⟪s⟫ t (ze r) = {!⟪z⟫!}
-- ⟪rec⟫ z ⟪z⟫ s ⟪s⟫ t (su r ⟪t⟫) = {!!}

-- Fundamental theorem

⟪_⟫ : (t : Tm Γ a) → Γ ∋G γ ® ρ → a ∋ clos t γ © ⦅ t ⦆ ρ
⟪ var x     ⟫ ⟪γ⟫     = laterR (lookupG ⟪γ⟫ x)
⟪ abs t     ⟫ ⟪γ⟫ ⟪u⟫ = laterR (⟪ t ⟫ (⟪u⟫ , ⟪γ⟫))
⟪ app t u   ⟫ ⟪γ⟫     = ⟪ t ⟫ ⟪γ⟫ (⟪ u ⟫ ⟪γ⟫)
⟪ ze        ⟫ ⟪γ⟫     = ze now
⟪ su t      ⟫ ⟪γ⟫     = su now (⟪ t ⟫ ⟪γ⟫)
⟪ rec z s t ⟫ ⟪γ⟫     = ⟪rec⟫ z (⟪ z ⟫ ⟪γ⟫) s (λ ⟪n⟫ ⟪a⟫ → ⟪ s ⟫ ((⟪a⟫ , ⟪n⟫ , ⟪γ⟫))) t (⟪ t ⟫ ⟪γ⟫)

-- ⟪ rec z s t ⟫ ⟪γ⟫ = ⟪rec⟫ (⟪ z ⟫ ⟪γ⟫) (λ ⟪n⟫ ⟪a⟫ → ⟪ s ⟫ ((⟪a⟫ , ⟪n⟫ , ⟪γ⟫))) (⟪ t ⟫ ⟪γ⟫)
-- ⟪ rec z s t ⟫ ⟪γ⟫ = case ⟪ t ⟫ ⟪γ⟫ of λ where
--   x → {!x!}

-- -}
