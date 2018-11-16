
module Term.Eval where

open import Prelude
open import Type
open import Term

Value : Type → Set
Value nat      = Nat
Value (a => b) = Value a → Value b

data Env : Context → Set where
  []  : Env []
  _∷_ : ∀ {Γ x a} → Value a → Env Γ → Env ((x , a) ∷ Γ)

natrecV : ∀ {A : Set} → A → (Nat → A → A) → Nat → A
natrecV z s zero = z
natrecV z s (suc n) = s n (natrecV z s n)

lookupEnv : ∀ {a Γ x} → x , a ∈ Γ → Env Γ → Value a
lookupEnv zero (v ∷ ρ) = v
lookupEnv (suc i) (_ ∷ ρ) = lookupEnv i ρ

eval : ∀ {Γ a} → Term Γ a → Env Γ → Value a
eval (var x i) ρ = lookupEnv i ρ
eval (lit n) ρ = n
eval suc ρ = suc
eval (app t t₁) ρ = eval t ρ (eval t₁ ρ)
eval (lam x t) ρ = λ v → eval t (v ∷ ρ)
eval (natrec a) ρ = natrecV
