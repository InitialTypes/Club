module Nat where

open import Data.Unit
open import Data.Empty
open import Data.Product

open import Relation.Binary
  using (Setoid)
open import Relation.Binary.Reasoning.MultiSetoid
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl)

infix 5 _+_
infix 4 _∼_
infix 4 _≈_
infix 4 _⟶_

-- Simple arithmetic expressions
data Exp : Set where
  z   : Exp
  s   : Exp → Exp
  _+_ : Exp → Exp → Exp

variable
  e e' e'' e1 e2 : Exp

-- Identities on expressions
data _∼_ : Exp → Exp → Set where
  z+ : z + e      ∼ e
  s+ : (s e) + e' ∼ s (e + e')

-- Equality on expressions
data _≈_ : Exp → Exp → Set where
  iden   : e ∼ e' → e ≈ e'
  refl   : e ≈ e
  sym    : e ≈ e' → e' ≈ e
  trans  : e ≈ e' → e' ≈ e'' → e ≈ e''
  cong-s : e ≈ e' → s e ≈ s e'
  cong-+ : e ≈ e1 → e' ≈ e2 → e + e' ≈ e1 + e2

Exp-setoid : Setoid _ _
Setoid.Carrier       Exp-setoid = Exp
Setoid._≈_           Exp-setoid = _≈_
Setoid.isEquivalence Exp-setoid = record { refl = refl ; sym = sym ; trans = trans }

-- `+` is associative
assoc : ∀ e1 e2 e3 → (e1 + e2) + e3 ≈ e1 + (e2 + e3)
assoc z           e2 e3 = begin⟨ Exp-setoid ⟩
  (z + e2) + e3
    ≈⟨ cong-+ (iden z+) refl ⟩
  e2 + e3
    ≈⟨ sym (iden z+) ⟩
  z + (e2 + e3)
    ∎
assoc (s e1)      e2 e3 = begin⟨ Exp-setoid ⟩
  ((s e1) + e2) + e3
    ≈⟨ cong-+ (iden s+) refl ⟩
  (s (e1 + e2)) + e3
    ≈⟨ iden s+ ⟩
  s ((e1 + e2) + e3)
    ≈⟨ cong-s (assoc e1 e2 e3) ⟩
  s (e1 + (e2 + e3))
    ≈⟨ sym (iden s+) ⟩
  (s e1) + (e2 + e3)
    ∎
assoc (e1 + e4) e2 e3 = begin⟨ Exp-setoid ⟩
  ((e1 + e4) + e2) + e3
    ≈⟨ trans (cong-+ (assoc e1 e4 e2) refl) (assoc e1 (e4 + e2) e3) ⟩
  e1 + ((e4 + e2) + e3)
    ≈⟨ cong-+ refl (assoc e4 e2 e3) ⟩
  e1 + (e4 + (e2 + e3))
    ≈⟨ sym (assoc e1 e4 (e2 + e3)) ⟩
  (e1 + e4) + (e2 + e3)
    ∎

-- Right unit law of `+`
z+' : ∀ e → e + z ≈ e
z+' z
  = iden z+
z+' (s e)
  = trans (iden s+) (cong-s (z+' e))
z+' (e + e')
  = trans (assoc e e' z) (cong-+ refl (z+' e'))


----------------
-- Normalization
----------------

-- Value predicate
IsVal : Exp → Set
IsVal z       = ⊤
IsVal (s e)   = IsVal e
IsVal (_ + _) = ⊥

-- Value expression (or normal form)
Val : Set
Val = Σ Exp IsVal

-- An expression to be reduced, aka a "redex"
data Redex : Set where

  -- `z+ e` denotes `z + e`
  z+ : Exp → Redex

  -- `s+ e e'` denotes `(s e) + e'`
  s+ : Exp → Exp → Redex

-- Rewrite a redex to an expression
re-write : Redex → Exp
re-write (z+ e)    = e
re-write (s+ e e') = s (e + e')

-- Evaluation Context
data EvalCtx : Set where
  ◯   : EvalCtx
  _+_  : EvalCtx → Exp → EvalCtx
  s    : EvalCtx → EvalCtx

-- Note: An evaluation context, as given here, can be understood as a "flipped"
-- expression with a hole (`◯`) in it, where the hole records the site of a redex.

-- Substitute the hole and flip the expression back
plug : EvalCtx → Exp → Exp
plug ◯        e = e
plug (c + e')  e = plug c (e + e')
plug (s c)     e = plug c (s e)

-- OBS: `plug` flips the expression by turning it inside out
_ : plug (s {-1-} (s {-2-} (◯ + z))) e ≡ (s {-2-} (s {-1-} e)) + z
_ = refl

-- Is reduction on a term done?
data Done? : Set where
  yes : Val → Done?
  no  : EvalCtx → Redex → Done?

-- Construct a redex for adding a value and an expression
mkRedex : Val → Exp → Redex
mkRedex (z   , _) e = z+ e
mkRedex (s t , _) e = s+ t e

-- Is a value done in the given context?
valDoneInCtx? : Val → EvalCtx → Done?
valDoneInCtx? v       ◯      = yes v
valDoneInCtx? v       (c + e) = no c (mkRedex v e)
valDoneInCtx? (t , p) (s c)   = valDoneInCtx? (s t , p) c

-- Is an expression done in the given context?
expDoneInCtx? : Exp → EvalCtx → Done?
expDoneInCtx? z        c = valDoneInCtx? (z , tt) c
expDoneInCtx? (s e)    c = expDoneInCtx? e (s c)
expDoneInCtx? (e + e') c = expDoneInCtx? e (c + e')

-- Is an expression done?
expDone? : Exp → Done?
expDone? e = expDoneInCtx? e ◯

-- Normalization function
{-# TERMINATING #-}
norm : Exp → Val
norm e with expDone? e
... | yes x   = x
... | no c r  = norm (plug c (re-write r))

----------------------------------
-- Normal-order reduction relation
----------------------------------

_⟶_ : Exp → Exp → Set
e ⟶ e' = ∃ λ (c : EvalCtx) → ∃ λ l → ∃ λ r
  → (e ≡ plug c l) × (e' ≡ plug c r) × l ∼ r

𝟘 : Exp
𝟘 = z

𝟙 : Exp
𝟙 = s 𝟘

_ : 𝟙 + 𝟘 ⟶ s (𝟘 + 𝟘)
_ = ◯ , (s z + z) , s (z + z) , refl , refl , s+

_ : s (𝟘 + 𝟘) ⟶ 𝟙
_ = s ◯ , z + z , z , refl , refl , z+

_ : norm (𝟙 + 𝟘) ≡ (𝟙 , _)
_ = refl

-- Q: Is _⟶_ deterministic?

----------------
-- NbE
----------------

-- Oh, and btw:

open import Data.Nat renaming (_+_ to _+ₙ_)

eval : Exp → ℕ
eval z        = 0
eval (s e)    = eval e +ₙ 1
eval (e + e') = eval e +ₙ eval e'

reify : ℕ → Val
reify zero    = (z , tt)
reify (suc n) = let (t , isVal) = reify n in (s t , isVal)

normByEval : Exp → Val
normByEval e = reify (eval e)
