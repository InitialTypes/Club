open import Library
open import Terms

module STLC where

Axioms : Set₁
Axioms = ∀{A} → (t t′ : Term ε A) → Set

module βη-Equality (𝓐 : Axioms) where
  data _≡λ_ : ∀{Γ A}  (t t′ : Term Γ A) → Set where
    -- (λ x. t) u = t [u / x]
    β : ∀{Γ A B} (t : Term (Γ , A) B) (u : Term Γ A) →
      (app (abs t) u) ≡λ (t /x← u)

    -- t = (λ x . t x)
    η : ∀{Γ A B} (t : Term Γ (A ⇒ B)) →
      t ≡λ abs (app (t ↓ suc) (var zero))

    -- (t,u) ∈ 𝓐 → t = u
    axiom : ∀{Γ A} (t u : Term ε A) → (i : ε ⊆ Γ) →
      𝓐 t u → (t ↓ i) ≡λ (u ↓ i)
    
    -- congruences
    λcong-abs : ∀{Γ A B} {t t′ : Term (Γ , A) B} →
      t ≡λ t′ → abs t ≡λ abs t′
    λcong-app : ∀{Γ A B} {t t′ : Term Γ (A ⇒ B)} {u u′ : Term Γ A} →
      t ≡λ t′ → u ≡λ u′ → app t u ≡λ app t′ u′

    -- equivalence closure
    λrefl : ∀{Γ A} {t : Term Γ A} →
      t ≡λ t
    λsym : ∀{Γ A} {t t′ : Term Γ A} →
      t ≡λ t′ → t′ ≡λ t
    λtrans : ∀{Γ A} {t t′ t″ : Term Γ A} →
      t ≡λ t′ → t′ ≡λ t″ → t ≡λ t″

-- plain βη-equality
_≡λ_ : ∀{Γ A} (t t′ : Term Γ A) → Set
_≡λ_ = βη-Equality._≡λ_ (λ _ _ → ⊥)


-- βη + axioms
_⊢_≡λ_ : (𝓐 : Axioms) → ∀{Γ A} (t t′ : Term Γ A) → Set
_⊢_≡λ_ = βη-Equality._≡λ_

record STLC-Semantics : Set₁ where
  field _⊨_ : (Γ : Context) (A : Type) → Set
  field ⟨_⟩ : ∀{Γ A} → (t : Term Γ A) → Γ ⊨ A
  -- equality of denotations
  _≡≡_ : ∀{Γ A} (t t′ : Term Γ A) → Set
  t ≡≡ u = ⟨ t ⟩ ≡ ⟨ u ⟩
  -- axioms hold semantically
  ⊨_ : (𝓐 : Axioms) → Set
  ⊨ 𝓐 = ∀{A} {t u : Term ε A} → 𝓐 t u → t ≡≡ u
  -- qualified meta-equality
  _⊨_≡≡_ : (𝓐 : Axioms) → ∀{Γ A} (t t′ : Term Γ A) → Set
  𝓐 ⊨ t ≡≡ u = (⊨ 𝓐) → t ≡≡ u

module STLC-Properties (sem : STLC-Semantics) where
  open STLC-Semantics sem

  weak-soundness : Set
  weak-soundness = ∀{Γ A} {t t′ : Term Γ A} → t ≡λ t′ → t ≡≡ t′

  weak-completeness : Set
  weak-completeness = ∀{Γ A} {t t′ : Term Γ A} → t ≡≡ t′ → t ≡λ t′

  soundness : Set₁
  soundness = ∀{𝓐 : Axioms} {Γ A} {t t′ : Term Γ A} → 𝓐 ⊢ t ≡λ t′ → 𝓐 ⊨ t ≡≡ t′

  completeness : Set₁
  completeness = ∀{𝓐 : Axioms} {Γ A} {t t′ : Term Γ A} → 𝓐 ⊨ t ≡≡ t′ → 𝓐 ⊢ t ≡λ t′


record STLC-Model : Set₁ where
  field sem : STLC-Semantics
  field soundness : STLC-Properties.soundness sem
