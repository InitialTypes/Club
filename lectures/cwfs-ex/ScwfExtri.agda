module ScwfExtri where

open import Data.Nat
open import UcwfExpSub

{-
Once you implement the untyped calculus of explicit substitutions, we
can add a type system
-}

data Ty : Set where
  o   : Ty
  _⇒_ : Ty → Ty → Ty
  
data Ctx : ℕ →  Set where
  ε   : Ctx 0
  _∙_ : {n : ℕ} → Ctx n → Ty → Ctx (suc n)


{- Exercise:

Add typing relations for terms and substitutions (mutually)


data _⊢_∈_ : ∀ {n} → Ctx n → Tm n → Ty → Set

data _▹_⊢_ : ∀ {m n} → Ctx m → Ctx n → Sub n m → Set


data _⊢_∈_ where

data _▹_⊢_ where
-}
