{-# OPTIONS --allow-unsolved-metas #-}

-- Newman's diamond lemma: Local confluence implies confluence for any
-- well-founded (or terminating) relation `R`.

module NewmansLemma {ℓ} {A : Set ℓ} (let Rel = A → A → Set ℓ) (R : Rel) where

private
  variable
    a a₁ a₂ a' : A
    b b₁ b₂ b' : A
    c c₁ c₂ c' : A
    r r₁ r₂ r' : R a b

-- Reflexive–transitive closure of `R`

data R* : Rel where
  nil  : R* a a
  cons : (r : R a b) → (rs : R* b c) → R* a c

refl : R* a a
refl = nil

singl : R a b → R* a b
singl r = cons r refl

trans : R* a b → R* b c → R* a c
trans nil         ss = ss
trans (cons r rs) ss = cons r (trans rs ss)

-- Joinable elements

data Joinable (a₁ a₂ : A) : Set ℓ where
  join : (rs₁ : R* a₁ b) → (rs₂ : R* a₂ b) → Joinable a₁ a₂

-- (Locally) confluent elements

LocConfl = λ a → ∀ {b₁ b₂} → (r₁  : R  a b₁) → (r₂  : R  a b₂) → Joinable b₁ b₂
Confl    = λ a → ∀ {b₁ b₂} → (rs₁ : R* a b₁) → (rs₂ : R* a b₂) → Joinable b₁ b₂

-- Accessible elements

data Acc (a : A) : Set ℓ where
  acc : (p : ∀ {b} → (r : R a b) → Acc b) → Acc a

-- Well-foundedness

WF = ∀ {a} → Acc a

-- Goal: prove Newman's diamond lemma:

newman's-lemma : WF → (∀{a} → LocConfl a) → ∀{a} → Confl a
newman's-lemma wf lc = {!!}

-- Hint: can maybe not be proven directly in this formulation,
-- may need auxiliary lemmata (and/or definitions).
