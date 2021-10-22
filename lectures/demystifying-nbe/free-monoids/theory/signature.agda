module free-monoids.theory.signature
  (X : Set)
  where

infixr 20 _•_
infix   3 _⊢_ _⊢Sub_

-- Types
data Ty : Set where
  ∗ : Ty -- \ast

variable
  a b c : Ty

-- Contexts
data Ctx : Set where
  []  : Ctx
  -- _,_ : (Γ : Ctx) → (a : Ty) → Ctx

variable
  Γ Γ' Γ'' : Ctx
  Δ Δ' Δ'' : Ctx
  Θ Θ' Θ'' : Ctx

-- Terms
data Tm : (Γ : Ctx) → (a : Ty) → Set

_⊢_ = Tm

data Tm where
  -- var :
  --       (n : Γ ⊢Var a) →
  --       ----------------
  --       Γ ⊢ a

  ⌜_⌝ : -- \cul \cur
        (x : X) →
        ----------------
        Γ ⊢ ∗

  _•_ : -- \bub -- maybe think `seq`, `bind`
        (t : Γ ⊢ ∗) →
        (u : Γ ⊢ ∗) →
        ----------------
        Γ ⊢ ∗

  e : -- maybe think `nop`, `return`

        ----------------
        Γ ⊢ ∗

variable
  t t' t'' : Tm Γ a
  u u' u'' : Tm Γ a
  v v' v'' : Tm Γ a
  w w' w'' : Tm Γ a

-- Substitutions
data Sub : (Δ Γ : Ctx) → Set

_⊢Sub_ = Sub

data Sub where
  tt  :

        ----------------
        Δ ⊢Sub []

  -- _,_ :
  --       (s : Δ ⊢Sub Γ) →
  --       (t : Δ ⊢    a) →
  --       ----------------
  --       Δ ⊢Sub Γ , a

variable
  s s' s'' : Sub Δ Γ
