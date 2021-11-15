-- Newman's lemma: Local confluence implies confluence
-- for any well-founded ( =terminating) relation R.

-- Variant without transitive closure (showed to me by David Wärn)

module NewmansLemma-opt {ℓ} {A : Set ℓ} (let Rel = A → A → Set ℓ) (R : Rel) where

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

data Joinable : Rel where
  join : (r₁ : R* a₁ a) (r₂ : R* a₂ a) → Joinable a₁ a₂

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

-- The Proof:

module Newman (lc : ∀{a} → LocConfl a) where

  lemma : Acc a → Confl a
  lemma (acc h) nil           nil         = join nil         nil
  lemma (acc h) nil           (cons r rs) = join (cons r rs) nil
  lemma (acc h) (cons r rs)   nil         = join nil         (cons r rs)
  lemma (acc h) (cons r₁ rs₁) (cons r₂ rs₂)
  --
  --     • r₂   • rs₂   •
  --     r₁    rs₄     rs₂'
  --     • rs₃  • rs₄'  •
  --    rs₁            rs₄''
  --     •     rs₁'     •
  --
      with lc r₁ r₂
  ... | join rs₃ rs₄
      with lemma (h r₂) rs₄ rs₂
  ... | join rs₄' rs₂'
      with lemma (h r₁) rs₁ (trans rs₃ rs₄')
  ... | join rs₁' rs₄''
      = join rs₁' (trans rs₂' rs₄'')

newman's-lemma wf lc = Newman.lemma lc wf
