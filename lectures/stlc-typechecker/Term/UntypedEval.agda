
module Term.UntypedEval where

open import Prelude
open import Type
open import Term

{-# NO_POSITIVITY_CHECK #-}  -- Cheating!
data Value : Set where
  nat   : Nat → Value
  fun   : (Value → Value) → Value
  error : String → Value

Env = List (Name × Value)

lookupVar : Name → Env → Value
lookupVar x [] = error $ "Unbound variable " & x
lookupVar x ((y , v) ∷ ρ) =
  ifYes x == y then v else lookupVar x ρ

vSuc : Value → Value
vSuc (nat n)   = nat (suc n)
vSuc (fun f)   = error "Cannot apply suc to function"
vSuc (error e) = error e

vApply : Value → Value → Value
vApply (nat n)   _ = error $ "Cannot apply number " & show n
vApply (fun f)   v = f v
vApply (error e) _ = error e

vNatrec' : Value → (Value → Value) → Nat → Value
vNatrec' z s zero = z
vNatrec' z s (suc n) = s (vNatrec' z s n)

vNatrec : Value
vNatrec = fun λ z → fun λ s → fun λ where
  (nat n)   → vNatrec' z (vApply s) n
  (fun _)   → error "Cannot apply natrec to function"
  (error e) → error e

eval : RawTerm → Env → Value
eval (var x)     ρ = lookupVar x ρ
eval (lit n)     ρ = nat n
eval suc         ρ = fun vSuc
eval (app t t₁)  ρ = vApply (eval t ρ) (eval t₁ ρ)
eval (lam x _ t) ρ = fun $ λ v → eval t ((x , v) ∷ ρ)
eval (natrec _)  ρ = vNatrec

-- ex₁ : RawTerm
-- ex₁ = lam "x" nat (app suc (var "x"))
