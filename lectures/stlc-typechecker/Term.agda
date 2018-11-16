--- === Top ===

{-

     A case study in dependently typed programming:
       Type checking the simply typed λ-calculus

                  Initial Types Club

                     Ulf Norell

                      ${TODAY}
-}

module Term where

open import Prelude























--- === Raw terms ===

open import Type

Name = String

-- λ-terms with natural numbers
data RawTerm : Set where
  var    : (x : Name) → RawTerm
  lit    : (n : Nat) → RawTerm
  suc    : RawTerm
  app    : (e e₁ : RawTerm) → RawTerm
  lam    : (x : Name) (a : Type) (e : RawTerm) → RawTerm
  natrec : (a : Type) → RawTerm

private
  -- λ (x : nat) → suc x
  ex₁ : RawTerm
  ex₁ = lam "x" nat (app suc (var "x"))

Context = List (Name × Type)

infix 3 _∈_
data _∈_ {A : Set} (x : A) : List A → Set where
  zero : ∀ {xs}                → x ∈ x ∷ xs
  suc  : ∀ {y xs} (i : x ∈ xs) → x ∈ y ∷ xs

data Term (Γ : Context) : Type → Set where
  var : ∀ {a} x (i : (x , a) ∈ Γ) → Term Γ a
  lit : (n : Nat) → Term Γ nat
  suc : Term Γ (nat => nat)
  app : ∀ {a b} → Term Γ (a => b) → Term Γ a → Term Γ b
  lam : ∀ {a b} x → Term ((x , a) ∷ Γ) b → Term Γ (a => b)
  natrec : (a : Type) → Term Γ (a => (nat => a => a) => nat => a)

forgetTypes : ∀ {Γ a} → Term Γ a → RawTerm
forgetTypes (var x i) = var x
forgetTypes (lit n) = lit n
forgetTypes suc = suc
forgetTypes (app u v) = app (forgetTypes u) (forgetTypes v)
forgetTypes (lam {a = a} x v) = lam x a (forgetTypes v)
forgetTypes (natrec a) = natrec a
