open import Library
open import Terms
open import STLC

open import Kripke.Semantics

module Kripke.Soundness (K : Kripke) where
open Semantics′ K
open import Kripke.Lemmas K
open STLC-Semantics sem hiding (⟨_⟩)
open βη-Equality
open ≡-Reasoning

is-sound′ : ∀{Γ A} {𝓐 : Axioms} {t t′ : Term Γ A} →
  𝓐 ⊢ t ≡λ t′ → (⊨ 𝓐) → ∀ {w} (γ : [ Γ ]* w) → ⟨ t ⟩ γ ≡ ⟨ t′ ⟩ γ
is-sound′ (axiom t u i x) hyp {w} γ = begin
  ⟨ t ↓ i ⟩ γ
  ≡⟨ weak-den t i γ ⟩
  ⟨ t ⟩ (i⟨ i ⟩ γ)
  ≡⟨ cong (λ t′ → t′ w tt) (hyp x)  ⟩
  ⟨ u ⟩ (i⟨ i ⟩ γ)
  ≡⟨ sym (weak-den u i γ) ⟩
  ⟨ u ↓ i ⟩ γ
  ∎
is-sound′ (β t u) hyp γ = begin
  ⟨ app (abs t) u ⟩ γ
  ≡⟨ law-app (abs t) u γ ⟩
  apply (⟨ abs t ⟩ γ) (⟨ u ⟩ γ)
  ≡⟨ cong (λ x → apply x (⟨ u ⟩ γ)) (sym (trans-id (⟨ abs t ⟩ γ))) ⟩
  apply (⟨ abs t ⟩ γ ↗ later-refl) (⟨ u ⟩ γ)
  ≡⟨ aux ⟩
  ⟨ t ⟩ (γ ↗* later-refl , ⟨ u ⟩ γ)
  ≡⟨ cong (λ x → ⟨ t ⟩ (x , ⟨ u ⟩ γ)) (trans*-id γ) ⟩
  ⟨ t ⟩ (γ , ⟨ u ⟩ γ)
  ≡⟨ cong (λ f → ⟨ t ⟩ (f γ , ⟨ u ⟩ γ)) (sym id-weak-den) ⟩
  ⟨ t ⟩ (i⟨ id ⟩ γ , ⟨ u ⟩ γ)
  ≡⟨ cong (λ γ′ → ⟨ t ⟩ (γ′ , ⟨ u ⟩ γ))  (sym (sub-weaken id γ)) ⟩
  ⟨ t ⟩ (σ⟨ var ⟩ γ , ⟨ u ⟩ γ)
  ≡⟨⟩
  ⟨ t ⟩ (σ⟨ sub u ⟩ γ)
  ≡⟨ sym (sub-den t (sub u) γ) ⟩
  ⟨ t / sub u ⟩ γ
  ∎
  where aux = law-apply-abs {p = later-refl}  t γ (⟨ u ⟩ γ)
is-sound′ (η t) hyp γ = law-ext (⟨ t ⟩ γ)
                                              (⟨ abs (app (t ↓ suc) (var zero)) ⟩ γ)
                                              λ p a → sym (begin
  apply (⟨ abs (app (t ↓ suc) (var zero)) ⟩ γ ↗ p) a
  ≡⟨ law-apply-abs (app (t ↓ suc) (var zero)) γ a ⟩
  ⟨ app (t ↓ suc) (var zero) ⟩ (γ ↗* p , a)
  ≡⟨ law-app (t ↓ suc) (var zero) (γ ↗* p , a) ⟩
  apply (⟨ t ↓ suc ⟩ (γ ↗* p , a)) (⟨ var zero ⟩ (γ ↗* p , a))
  ≡⟨ cong (λ v → apply (⟨ t ↓ suc ⟩ (γ ↗* p , a)) v) (law-var zero (γ ↗* p , a)) ⟩
  apply (⟨ t ↓ suc ⟩ (γ ↗* p , a)) a
  ≡⟨ cong (λ t → apply t a) (weak-den t suc (γ ↗* p , a)) ⟩
  apply (⟨ t ⟩ (i⟨ suc ⟩ (γ ↗* p , a))) a
  ≡⟨ cong (λ i → apply (⟨ t ⟩ (i (γ ↗* p , a))) a) (lift-weak-den id) ⟩
  apply (⟨ t ⟩ (i⟨ id ⟩ (γ ↗* p))) a
  ≡⟨ cong (λ i → apply (⟨ t ⟩ (i (γ ↗* p))) a) id-weak-den ⟩
  apply (⟨ t ⟩ (γ ↗* p)) a
  ≡⟨ cong (λ x → apply x a) (trans-den t γ p) ⟩
  apply (⟨ t ⟩ γ ↗ p) a
  ∎)
is-sound′ (λcong-abs {t = t} {t′ = t′} eq) hyp γ =
  law-ext (⟨ abs t ⟩ γ) (⟨ abs t′ ⟩ γ) λ p a → begin
  apply (⟨ abs t ⟩ γ ↗ p) a
  ≡⟨ law-apply-abs t γ a ⟩
  ⟨ t ⟩ (γ ↗* p , a)
  ≡⟨ is-sound′ eq hyp (γ ↗* p , a) ⟩
  ⟨ t′ ⟩ (γ ↗* p , a)
  ≡⟨ sym (law-apply-abs t′ γ a) ⟩
  apply (⟨ abs t′ ⟩ γ ↗ p) a
  ∎
is-sound′ (λcong-app {Γ} {A} {B} {t} {t′} {u} {u′} eq eq₁) hyp γ = begin
  ⟨ app t u ⟩ γ
  ≡⟨ law-app t u γ ⟩
  apply (⟨ t ⟩ γ) (⟨ u ⟩ γ)
  ≡⟨ cong₂ apply (is-sound′ eq hyp γ) (is-sound′ eq₁ hyp γ) ⟩
  apply (⟨ t′ ⟩ γ) (⟨ u′ ⟩ γ)
  ≡⟨ sym (law-app t′ u′ γ) ⟩
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
