-- Newman's lemma: Local confluence implies confluence
-- for any well-founded ( =terminating) relation R.

module NewmansLemma {ℓ} {A : Set ℓ} (let Rel = A → A → Set ℓ) (R : Rel) where

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
newman's-lemma = {!!}

-- Hint: cannot proven directly in this formulation, needs auxiliary lemmata and definitions.
