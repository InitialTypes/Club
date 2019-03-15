open import Library
open import Terms
open import STLC

open import Henkin.Semantics

module Henkin.Soundness (H : Henkin) where
open Semantics′ H
open import Henkin.Lemmas H
open βη-Equality
open ≡-Reasoning

-- only up to extensionality!
is-sound′ : ∀{Γ A} {𝓐 : Axioms} {t t′ : Term Γ A} →
  𝓐 ⊢ t ≡λ t′ → (∀{A} {t u : Term ε A} → 𝓐 t u → ⟨ t ⟩ ≡ ⟨ u ⟩)
  → ∀ γ → ⟨ t ⟩ γ ≡ ⟨ t′ ⟩ γ
is-sound′ (axiom t u j x) hyp γ = begin
  ⟨ t ↓ j ⟩ γ
  ≡⟨ weak-den t j γ ⟩
  ⟨ t ⟩ (i⟨ j ⟩ γ)
  ≡⟨ cong-app (hyp x) (i⟨ j ⟩ γ) ⟩
  ⟨ u ⟩ (i⟨ j ⟩ γ)
  ≡⟨ sym (weak-den u j γ) ⟩
  ⟨ u ↓ j ⟩ γ
  ∎
is-sound′ (β t u) hyp γ = begin
  ⟨ app (abs t) u ⟩ γ
  ≡⟨ law-app (abs t) u γ ⟩
  apply (⟨ abs t ⟩ γ) (⟨ u ⟩ γ)
  ≡⟨ law-apply-abs t γ (⟨ u ⟩ γ) ⟩
  ⟨ t ⟩ (γ , ⟨ u ⟩ γ)
  ≡⟨ cong (λ x → ⟨ t ⟩ (x γ , ⟨ u ⟩ γ)) (sym id-weak-den) ⟩
  ⟨ t ⟩ (i⟨ id ⟩ γ , ⟨ u ⟩ γ)
  ≡⟨ cong (λ x → ⟨ t ⟩ (x , ⟨ u ⟩ γ)) (sym (sub-weaken id γ)) ⟩
  ⟨ t ⟩ (σ⟨ var ⟩ γ , ⟨ u ⟩ γ)
  ≡⟨⟩
  (⟨ t ⟩ ∘ σ⟨ sub u ⟩) γ
  ≡⟨ sym (sub-den t (sub u) γ) ⟩
  ⟨ t /x← u ⟩ γ
  ∎
is-sound′ (η t) hyp γ
  = law-ext (⟨ t ⟩ γ) (⟨ abs (app (t ↓ suc) (var zero)) ⟩ γ)
            λ a → sym (begin
  apply (⟨ abs (app (t ↓ suc) (var zero)) ⟩ γ) a
  ≡⟨ law-apply-abs (app (t ↓ (λ {A} → suc)) (var zero)) γ a ⟩
  ⟨ app (t ↓ suc) (var zero) ⟩ (γ , a)
  ≡⟨ law-app (t ↓ (λ {A} → suc)) (var zero) (γ , a) ⟩
  apply (⟨ t ↓ suc ⟩ (γ , a)) (⟨ var zero ⟩ (γ , a))
  ≡⟨ cong (λ x → apply x (⟨ var zero ⟩ (γ , a))) (weak-den t suc (γ , a)) ⟩
  apply (⟨ t ⟩ (i⟨ suc ⟩ (γ , a))) (⟨ var zero ⟩ (γ , a))
  ≡⟨ cong (λ x → apply (⟨ t ⟩ (x (γ , a))) (⟨ var zero ⟩ (γ , a))) (lift-weak-den id) ⟩
  apply (⟨ t ⟩ (i⟨ id ⟩ γ)) (⟨ var zero ⟩ (γ , a))
  ≡⟨ cong (λ x → apply (⟨ t ⟩ (x γ)) (⟨ var zero ⟩ (γ , a))) id-weak-den ⟩
  apply (⟨ t ⟩ γ) (⟨ var zero ⟩ (γ , a))
  ≡⟨ cong (λ x → apply (⟨ t ⟩ γ) x) (law-var zero (γ , a)) ⟩
  apply (⟨ t ⟩ γ) a
  ∎)
is-sound′ (λcong-abs {t = t} {t′ = t′} eq) hyp γ
  = law-ext (⟨ abs t ⟩ γ) (⟨ abs t′ ⟩ γ)
            λ a → begin
  apply (⟨ abs t ⟩ γ) a
  ≡⟨ law-apply-abs t γ a ⟩
  ⟨ t ⟩ (γ , a)
  ≡⟨ is-sound′ eq hyp (γ , a) ⟩
  ⟨ t′ ⟩ (γ , a)
  ≡⟨ sym (law-apply-abs t′ γ a) ⟩
  apply (⟨ abs t′ ⟩ γ) a
  ∎
is-sound′ (λcong-app {Γ} {A} {B} {t} {t′} {u} {u′} eq eq₁) hyp γ = begin
  ⟨ app t u ⟩ γ
  ≡⟨ law-app t u γ ⟩
  apply (⟨ t ⟩ γ) (⟨ u ⟩ γ)
  ≡⟨ cong₂ apply (is-sound′ eq hyp γ)
                 (is-sound′ eq₁ hyp γ) ⟩
  apply (⟨ t′ ⟩ γ) (⟨ u′ ⟩ γ)
  ≡⟨ sym (law-app t′ u′ γ ) ⟩
  ⟨ app t′ u′ ⟩ γ
  ∎
is-sound′ λrefl hyp γ = refl
is-sound′ (λsym eq) hyp γ = sym (is-sound′ eq hyp γ)
is-sound′ (λtrans {Γ} {A} {t} {t′} {t″} eq eq₁) hyp γ = begin
  ⟨ t ⟩ γ
  ≡⟨ is-sound′ eq hyp γ ⟩
  ⟨ t′ ⟩ γ
  ≡⟨ is-sound′ eq₁ hyp γ ⟩
  ⟨ t″ ⟩ γ
  ∎
