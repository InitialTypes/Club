open import Library
open import Terms
open import STLC

open import Standard.Semantics

module Standard.Lemmas where

{- Weakening -}
-- recover definitional equality
lift-weak-den : ∀{Γ Δ B} → (i : Γ ⊆ Δ) → i⟨ suc {B = B} ∘ i ⟩ ≡ i⟨ i ⟩ ∘ proj₁
lift-weak-den {ε} i = refl
lift-weak-den {Γ , A} {Δ} {B} i
  rewrite lift-weak-den {B = B} (i ∘ suc)
          = refl

-- recover definitional equality
id-weak-den : ∀{Γ} → i⟨ (λ {A} (v : Var Γ A) → v) ⟩ ≡ (λ γ → γ)
id-weak-den {ε} = refl
id-weak-den {Γ , A}
  rewrite lift-weak-den {Γ} {Γ} {A} (λ x → x) |
          id-weak-den {Γ}
          = refl


weakv-den : ∀{Γ A Δ} (v : Var Γ A) (i : Γ ⊆ Δ) →
  v⟨ i v ⟩ ≡ v⟨ v ⟩ ∘ i⟨ i ⟩
weakv-den zero i = refl
weakv-den (suc v) i = weakv-den v (i ∘ suc)

weak-den : ∀{Γ A Δ} (t : Term Γ A) (i : Γ ⊆ Δ) →
  ⟨ t ↓ i ⟩ ≡ ⟨ t ⟩ ∘ i⟨ i ⟩
weak-den (var v) i = weakv-den v i
weak-den (abs {A = A} t) i
  rewrite weak-den t (↑⊆ i) |
          lift-weak-den {B = A} i
          = refl
weak-den (app t u) i
  rewrite weak-den t i |
          weak-den u i
          = refl

weak-den-comp : ∀{Γ Δ Ω} (i : Δ ⊆ Ω) (i′ : Γ ⊆ Δ) →
  i⟨ i ∘ i′ ⟩ ≡ i⟨ i′ ⟩ ∘ i⟨ i ⟩
weak-den-comp {ε} i i′ = refl
weak-den-comp {Γ , A} i i′
  rewrite weakv-den (i′ zero) i |
          weak-den-comp i (i′ ∘ suc)
          = refl


{- Substitution -}
subv-den : ∀{Γ A Δ}(v : Var Γ A)(σ : Γ ≤ Δ) →
  ⟨ σ v ⟩ ≡ v⟨ v ⟩ ∘ σ⟨ σ ⟩
subv-den zero i = refl
subv-den (suc v) i = subv-den v (i ∘ suc)

weakσ-den : ∀{Γ Δ Ω} (σ : Γ ≤ Δ) (i : Δ ⊆ Ω) →
  σ⟨ (λ v → σ v ↓ i) ⟩ ≡ σ⟨ σ ⟩ ∘ i⟨ i ⟩
weakσ-den {ε} σ i = refl
weakσ-den {Γ , A} σ i
  rewrite weakσ-den (σ ∘ suc) i |
          weak-den (σ zero) i
          = refl

sub-den : ∀{Γ A Δ}(t : Term Γ A)(σ : Γ ≤ Δ) →
  ⟨ t / σ ⟩ ≡ ⟨ t ⟩ ∘ σ⟨ σ ⟩
sub-den (var v) σ = subv-den v σ
sub-den {Δ = Δ} (abs {Γ} {A = A} {B = B} t) σ
  rewrite sub-den t (↑σ σ) |
          weakσ-den σ (suc {B = A}) |
          lift-weak-den {Δ} {Δ} {A} (λ x → x) |
          id-weak-den {Δ}
          = refl
sub-den (app t u) σ
  rewrite sub-den t σ |
          sub-den u σ
          = refl

sub-weaken : ∀{Γ Δ} (i : Γ ⊆ Δ) → σ⟨ var ∘ i ⟩ ≡ i⟨ i ⟩
sub-weaken {ε} i = refl
sub-weaken {Γ , A} i
  rewrite sub-weaken (i ∘ suc)
          = refl

