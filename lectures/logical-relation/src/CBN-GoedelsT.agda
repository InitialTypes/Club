-- A sound interpreter for Gödel's T in combinatory logic style

open import Size

open import Category.Monad           using (module RawMonad)
open import Codata.Delay             using (Delay; now; later)
open import Codata.Delay.Categorical using (module Sequential)
open import Codata.Thunk             using (Thunk; force)

open import Data.Empty        using (⊥; ⊥-elim)
open import Data.List         using (List; []; _∷_)
open import Data.Nat.Base     using (ℕ; zero; suc)
open import Data.Product      using (∃; _,_; proj₁; proj₂)

open import Data.List.Membership.Propositional public using (_∈_)
open import Data.List.Relation.Unary.All public using (All; []; _∷_) hiding (module All)
open import Data.List.Relation.Unary.Any public using (here; there)

open import Function using (case_of_)

open import Relation.Nullary  using (¬_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
                              using (Star; ε; _▻_; _◅_)

open import Relation.Binary.PropositionalEquality public using (_≡_; refl)

pattern here! = here refl

module All where
  open import Data.List.Relation.Unary.All public

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
  d d'            : ⟦ a ⟧
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
    inductive; constructor clos -- _⊢_
    field
      {cxt} : Cxt
      env   : Env cxt
      tm    : Tm cxt a

-- infix 7 _⊢_

variable
  γ γ' δ δ' : Env Γ
  cl cl'    : Clos a

-- CBN values

data Val : Ty → Set where
  abs :  (δ : Env Δ) (t : Tm (a ∷ Δ) b) → Val (a ⇒ b)
  ze  : Val nat
  su  : (cl : Clos nat) → Val nat

variable
  v w : Val a

-- Call-by-name interpreter

-- infix 2 _↘_

variable
  i : Size

mutual
  eval : ∀{i} → Env Γ → Tm Γ a → Delay (Val a) i
  eval γ (var x)      = later (evalCl' (All.lookup γ x))
  eval γ (abs t)      = now (abs γ t)
  eval γ (app t u)    = do
    abs δ t' ← eval γ t
    later (eval' (clos γ u ∷ δ) t')
    where open RawMonad Sequential.monad

  eval γ ze           = now ze
  eval γ (su t)       = now (su (clos γ t))
  eval γ (rec z s t)  =
    eval γ t >>= λ where
      ze       → eval γ z
      (su cl)  → eval (clos γ (rec z s t) ∷ cl ∷ γ) s
    where open RawMonad Sequential.monad

  eval' : ∀{i} → Env Γ → Tm Γ a → Thunk (Delay (Val a)) i
  eval' γ t .force = eval γ t

  -- apply : Val (a ⇒ b) → Clos a →

  -- evalCl : ∀{i} → Clos a → Delay (Val a) i
  -- evalCl (clos γ t) = eval γ t
  -- -- evalCl (γ ⊢ t) = eval γ t

  evalCl' : ∀{i} → Clos a → Thunk (Delay (Val a)) i
  evalCl' (clos γ t) = eval' γ t

-- -}
