--- === Top ===

module TypeCheck where

open import Prelude
open import Container.Traversable
open import Type
open import Term
open import Term.Show
open import Term.Parse

--- === The type checker ===

TC : Set → Set
TC A = Either String A

fail : {A : Set} → String → TC A
fail = left

data WellTyped Γ : RawTerm → Set where
  ok : (a : Type) (t : Term Γ a) → WellTyped Γ (forgetTypes t)

infix 2 _∷:_
pattern _∷:_ t a = ok a t

data InScope (Γ : Context) x : Set where
  ok : ∀ a → (x , a) ∈ Γ → InScope Γ x

lookupVar : ∀ Γ x → TC (InScope Γ x)
lookupVar [] x = fail $ "Variable out of scope: " & x
lookupVar ((y , a) ∷ Γ) x with x == y
... | yes refl = pure (ok a zero)
... | no _     = do
  ok b i ← lookupVar Γ x
  pure (ok b (suc i))

_=?=_ : (a b : Type) → TC (a ≡ b)
a =?= b with a == b
... | yes p = pure p
... | no _  = fail $ show a & " != " & show b

infer : (Γ : Context) (e : RawTerm) → TC (WellTyped Γ e)
infer Γ (var x) = do
  ok a i ← lookupVar Γ x
  pure (var x i ∷: a)
infer Γ (lit n) = pure (lit n ∷: nat)
infer Γ suc = pure (suc ∷: nat => nat)
infer Γ (app e e₁) = do
  u ∷: a => b ← infer Γ e
    where u ∷: nat → fail $ "Nat is not a function, silly: " & show u
  v ∷: a₁ ← infer Γ e₁
  refl ← a =?= a₁
  pure (app u v ∷: b)
infer Γ (lam x a e) = do
  t ∷: b ← infer ((x , a) ∷ Γ) e
  pure (lam x t ∷: a => b)
infer Γ (natrec a) = pure (natrec a ∷: _)

--- === Forgetting the raw terms ===

TypedTerm : Context → Set
TypedTerm Γ = Σ Type (Term Γ)

forgetRaw : ∀ {Γ e} → WellTyped Γ e → TypedTerm Γ
forgetRaw (ok a t) = a , t

checkString : String → TC (TypedTerm [])
checkString s =
  case parseTerm s of λ where
    nothing  → fail $ "Parse error on: " & s
    (just e) → forgetRaw <$> infer [] e

applyArgs : ∀ {Γ} → TypedTerm Γ → List (TypedTerm Γ) → TC (TypedTerm Γ)
applyArgs t [] = pure t
applyArgs (a => b , f) ((a₁ , v) ∷ vs) = do
  refl ← a =?= a₁
  applyArgs (b , app f v) vs
applyArgs (a , v) _ = fail $ "Too many arguments to " & show v & " of type " & show a

checkStrings : String → List String → TC (TypedTerm [])
checkStrings f args = do
  f    ← checkString f
  args ← traverse checkString args
  applyArgs f args

--- === Overkill ===

data WellTyped' (Γ : Context) (s : String) : Set where
  ok : ∀ (e : RawTerm) (v : WellTyped Γ e) → parseTerm s ≡ just e → WellTyped' Γ s

checkString' : (s : String) → TC (WellTyped' [] s)
checkString' s with parseTerm s | graphAt parseTerm s
... | nothing | _ = fail $ "Parse error on: " & s
... | just e  | ingraph eq = do
  v <- infer [] e
  pure (ok e v eq)
