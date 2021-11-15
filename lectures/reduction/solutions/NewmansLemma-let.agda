-- Newman's lemma: Local confluence implies confluence
-- for any well-founded ( =terminating) relation R.

-- Variant with "let...in..."

module NewmansLemma-let {ℓ} {A : Set ℓ} (let Rel = A → A → Set ℓ) (R : Rel) where

variable
  a a₁ a₂ a' : A
  b b₁ b₂ b' : A
  c c₁ c₂ c' : A
  r r₁ r₂ r' : R a b

-- Reflexive transitive closure

data R* : Rel where
  nil   : R* a a
  cons  : R  a b → R* b c → R* a c

trans : R* a b → R* b c → R* a c
trans nil         ss = ss
trans (cons r rs) ss = cons r (trans rs ss)

-- Joinable elements

record Joinable (a₁ a₂ : A) : Set ℓ where
  constructor join
  field
    {a₀}  : A
    left  : R* a₁ a₀
    right : R* a₂ a₀

-- (Locally) confluent

LocConfl = λ a → ∀ {a₁ a₂} → R  a a₁ → R  a a₂ → Joinable a₁ a₂
Confl    = λ a → ∀ {a₁ a₂} → R* a a₁ → R* a a₂ → Joinable a₁ a₂

-- Accessible elements

data Acc : A → Set ℓ where
  acc : (∀{b} (r : R a b) → Acc b) → Acc a

-- Wellfoundedness

WF = ∀{a} → Acc a

-- Goal: prove Newman's Lemma:

newman's-lemma : WF → (∀{a} → LocConfl a) → ∀{a} → Confl a

-- Transitive closure

data R⁺ : Rel where
  cons : R  a b → R* b c → R⁺ a c

sg : R a b → R⁺ a b
sg r = cons r nil

-- Accessible elements wrt. transitive closure

data Acc⁺ : A → Set ℓ where
  acc : (∀{b} (r : R⁺ a b) → Acc⁺ b) → Acc⁺ a

-- Lemma: If an element is accessible wrt. R, then also wrt. R⁺

wf⁺ : Acc a → R⁺ a b → Acc⁺ b
wf⁺ (acc h) (cons r rs) = wf* (h r) rs
  where
  wf* : Acc a → R* a b → Acc⁺ b
  wf* (acc h) nil = acc (wf⁺ (acc h))
  wf* (acc h) (cons r rs) = wf* (h r) rs

-- The Proof:

module Newman (lc : ∀{a} → LocConfl a) where

  lemma : Acc⁺ a → Confl a
  lemma (acc h) nil           nil         = join nil         nil
  lemma (acc h) nil           (cons r rs) = join (cons r rs) nil
  lemma (acc h) (cons r rs)   nil         = join nil         (cons r rs)
  lemma (acc h) (cons r₁ rs₁) (cons r₂ rs₂) = let
  --
  --     • r₂   • rs₂   •
  --     r₁    rs₄     rs₂'
  --     • rs₃  • rs₄'  •
  --    rs₁    rs₃'    rs₄''
  --     • rs₁' • rs₃'' •
  --
      join rs₃   rs₄   = lc r₁ r₂
      join rs₁'  rs₃'  = lemma (h (sg r₁)) rs₁ rs₃
      join rs₄'  rs₂'  = lemma (h (sg r₂)) rs₄ rs₂
      join rs₃'' rs₄'' = lemma (h (cons r₂ rs₄)) rs₃' rs₄'
      in
      join (trans rs₁' rs₃'') (trans rs₂' rs₄'')

newman's-lemma wf lc = Newman.lemma lc (acc (wf⁺ wf))
