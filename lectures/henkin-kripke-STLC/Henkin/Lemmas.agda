open import Library
open import Terms
open import STLC

open import Henkin.Semantics

module Henkin.Lemmas (H : Henkin) where
open Semantics′ H
open ≡-Reasoning

weakv-den : ∀{Γ A Δ} (v : Var Γ A) (i : Γ ⊆ Δ) →
  v⟨ i v ⟩ ≡ v⟨ v ⟩ ∘ i⟨ i ⟩
weakv-den zero i = refl
weakv-den (suc v) i = weakv-den v (i ∘ suc)

weak-den-comp : ∀{Γ Δ Ω} (i : Δ ⊆ Ω) (i′ : Γ ⊆ Δ) →
  i⟨ i ∘ i′ ⟩ ≡ i⟨ i′ ⟩ ∘ i⟨ i ⟩
weak-den-comp {ε} i i′ = refl
weak-den-comp {Γ , A} i i′ = begin
  i⟨ i ∘ i′ ⟩
  ≡⟨⟩
  (λ δ → i⟨ i ∘ i′ ∘ suc ⟩ δ , v⟨ (i ∘ i′) zero ⟩ δ)
  ≡⟨ cong (λ f δ → f δ , v⟨ (i ∘ i′) zero ⟩ δ ) (weak-den-comp i (i′ ∘ suc)) ⟩
  (λ δ → i⟨ i′ ∘ suc ⟩ (i⟨ i ⟩ δ) , v⟨ (i ∘ i′) zero ⟩ δ)
  ≡⟨ cong (λ x δ → (i⟨ i′ ∘ suc ⟩ (i⟨ i ⟩ δ)) , (x δ)) (weakv-den (i′ zero) i)⟩
  (λ δ → i⟨ i′ ∘ suc ⟩ (i⟨ i ⟩ δ) , v⟨ i′ zero ⟩ (i⟨ i ⟩ δ))
  ≡⟨⟩
  i⟨ i′ ⟩ ∘ i⟨ i ⟩
  ∎

lift-weak-den : ∀{Γ Δ B} → (i : Γ ⊆ Δ) → i⟨ suc {B = B} ∘ i ⟩ ≡ i⟨ i ⟩ ∘ proj₁
lift-weak-den {ε} i = refl
lift-weak-den {Γ , A} {Δ} {B} i = begin
  i⟨ suc ∘ i ⟩
  ≡⟨⟩
  (λ δ → i⟨ suc ∘ i ∘ suc ⟩ δ , v⟨ i zero ⟩ (proj₁ δ))
  ≡⟨ cong (λ x δ → (x δ) , (v⟨ i zero ⟩ (proj₁ δ))) (lift-weak-den {B = B} (i ∘ suc)) ⟩
  (λ δ → i⟨ i ∘ suc ⟩ (proj₁ δ) , v⟨ i zero ⟩ (proj₁ δ))
  ≡⟨⟩
  i⟨ i ⟩ ∘ proj₁
  ∎

id-weak-den : ∀{Γ} → i⟨ id ⟩ ≡ id {A = [ Γ ]*}
id-weak-den {ε} = refl
id-weak-den {Γ , A} rewrite lift-weak-den {Γ} {Γ} {A} id |
                    id-weak-den {Γ} = refl

weak-den : ∀{Γ A Δ}(t : Term Γ A)(i : Γ ⊆ Δ) →
  (δ : [ Δ ]*) → ⟨ t ↓ i ⟩ δ ≡ (⟨ t ⟩ ∘ i⟨ i ⟩) δ
weak-den (var v) i δ = begin
  ⟨ var v ↓ i ⟩ δ
  ≡⟨ law-var (i v) δ ⟩
  v⟨ i v ⟩ δ
  ≡⟨ cong-app (weakv-den v i) δ ⟩
  v⟨ v ⟩ (i⟨ i ⟩ δ)
  ≡⟨ sym (law-var v (i⟨ i ⟩ δ)) ⟩
  (⟨ var v ⟩ ∘ i⟨ i ⟩) δ
  ∎
weak-den (abs {A = A} t) i δ = law-ext (⟨ abs t ↓ i ⟩ δ) (⟨ abs t ⟩ (i⟨ i ⟩ δ))
                                       (λ a → begin
  apply (⟨ (abs t) ↓ i ⟩ δ) a
  ≡⟨⟩
  apply (⟨ abs (t ↓ ↑⊆ i) ⟩ δ) a
  ≡⟨ law-apply-abs (t ↓ ↑⊆ i) δ a  ⟩
  ⟨ t ↓ ↑⊆ i ⟩ (δ , a)
  ≡⟨ weak-den t (↑⊆ i) (δ , a) ⟩
  ⟨ t ⟩ (i⟨ ↑⊆ i ⟩ (δ , a))
  ≡⟨ cong (λ f → ⟨ t ⟩ (f (δ , a) , a)) (lift-weak-den i) ⟩
  ⟨ t ⟩ (i⟨ i ⟩ δ , a)
  ≡⟨ sym (law-apply-abs t (i⟨ i ⟩ δ) a) ⟩
     apply ((⟨ abs t ⟩ ∘ i⟨ i ⟩) δ) a
  ∎)
weak-den (app t u) i δ = begin
  ⟨ app t u ↓ i ⟩ δ
  ≡⟨⟩
  ⟨ app (t ↓ i) (u ↓ i) ⟩ δ
  ≡⟨ law-app (t ↓ i) (u ↓ i) δ ⟩
  apply (⟨ t ↓ i ⟩ δ) (⟨ u ↓ i ⟩ δ)
  ≡⟨ cong₂ (λ t u → apply t u) (weak-den t i δ) (weak-den u i δ) ⟩
  apply (⟨ t ⟩ (i⟨ i ⟩ δ)) (⟨ u ⟩ (i⟨ i ⟩ δ))
  ≡⟨ sym (law-app t u (i⟨ i ⟩ δ) ) ⟩
  (⟨ app t u ⟩ ∘ i⟨ i ⟩) δ
  ∎

sub-weaken : ∀{Γ Δ} (i : Γ ⊆ Δ) →
  (δ : [ Δ ]*) → σ⟨ var ∘ i ⟩ δ ≡ i⟨ i ⟩ δ
sub-weaken {ε} i δ = refl
sub-weaken {Γ , A} i δ = begin
  σ⟨ var ∘ i ⟩ δ
  ≡⟨⟩
  σ⟨ var ∘ i ∘ suc ⟩ δ , ⟨ var (i zero) ⟩ δ
  ≡⟨ cong₂ _,_ (sub-weaken (i ∘ suc) δ) (law-var (i zero) δ) ⟩
  i⟨ i ⟩ δ
  ∎

weakσ-den : ∀{Γ Δ Ω} (σ : Γ ≤ Δ) (i : Δ ⊆ Ω) →
  (ω : [ Ω ]*) → σ⟨ (λ v → σ v ↓ i) ⟩ ω ≡ σ⟨ σ ⟩ (i⟨ i ⟩ ω)
weakσ-den {ε} σ i δ = refl
weakσ-den {Γ , A} σ i δ = begin
  σ⟨ (λ v → σ v ↓ i) ⟩ δ
  ≡⟨⟩
  σ⟨ (λ v → (σ ∘ suc) v ↓ i) ⟩ δ , ⟨ σ zero ↓ i ⟩ δ
  ≡⟨ cong₂ (λ x y → x , y) (weakσ-den (σ ∘ suc) i δ) (weak-den (σ zero) i δ) ⟩
  (σ⟨ σ ∘ suc ⟩ ∘ i⟨ i ⟩) δ , ⟨ σ zero ⟩ (i⟨ i ⟩ δ)
  ≡⟨⟩
  (σ⟨ σ ⟩ ∘ i⟨ i ⟩) δ
  ∎

subv-den : ∀{Γ A Δ}(v : Var Γ A)(σ : Γ ≤ Δ) →
  ⟨ σ v ⟩ ≡ v⟨ v ⟩ ∘ σ⟨ σ ⟩
subv-den zero i = refl
subv-den (suc v) i = subv-den v (i ∘ suc)

sub-den : ∀{Γ A Δ}(t : Term Γ A)(σ : Γ ≤ Δ) →
  (δ : [ Δ ]*) → ⟨ t / σ ⟩ δ ≡ (⟨ t ⟩ ∘ σ⟨ σ ⟩) δ
sub-den (var v) σ δ = begin
  ⟨ var v / σ ⟩ δ
  ≡⟨⟩
  ⟨ σ v ⟩ δ
  ≡⟨ cong-app (subv-den v σ) δ ⟩
  (v⟨ v ⟩ ∘ σ⟨ σ ⟩) δ
  ≡⟨ sym (law-var v (σ⟨ σ ⟩ δ)) ⟩
  (⟨ var v ⟩ ∘ σ⟨ σ ⟩) δ
  ∎
sub-den {Δ = Δ} (abs {Γ} {A = A} {B = B} t) σ δ
  = law-ext (⟨ abs t / σ ⟩ δ) (⟨ abs t ⟩ (σ⟨ σ ⟩ δ))
            λ x → begin
  apply (⟨ abs t / σ ⟩ δ) x
  ≡⟨⟩
  apply (⟨ abs (t / ↑σ σ) ⟩ δ) x
  ≡⟨ law-apply-abs (t / ↑σ σ) δ x ⟩
  ⟨ t / ↑σ σ ⟩ (δ , x)
  ≡⟨ sub-den t (↑σ σ) (δ , x) ⟩
  ⟨ t ⟩ (σ⟨ ↑σ σ ⟩ (δ , x))
  ≡⟨⟩
  ⟨ t ⟩ (σ⟨ (λ v → σ v ↓ suc) ⟩ (δ , x) , ⟨ var zero ⟩ (δ , x))
  ≡⟨ cong (λ y → ⟨ t ⟩ (y , ⟨ var zero ⟩ (δ , x))) (weakσ-den σ suc (δ , x)) ⟩
  ⟨ t ⟩ (σ⟨ σ ⟩ (i⟨ suc ⟩ (δ , x)) , ⟨ var zero ⟩ (δ , x))
  ≡⟨ cong (λ y → ⟨ t ⟩ (σ⟨ σ ⟩ (y (δ , x)) , ⟨ var zero ⟩ (δ , x))) (lift-weak-den id) ⟩
  ⟨ t ⟩ (σ⟨ σ ⟩ (i⟨ id ⟩ δ) , ⟨ var zero ⟩ (δ , x))
  ≡⟨ cong (λ y → ⟨ t ⟩ (σ⟨ σ ⟩ (y δ) , ⟨ var zero ⟩ (δ , x))) id-weak-den ⟩
  ⟨ t ⟩ (σ⟨ σ ⟩ δ , ⟨ var zero ⟩ (δ , x))
  ≡⟨ cong (λ y → ⟨ t ⟩ (σ⟨ σ ⟩ δ , y)) (law-var zero (δ , x)) ⟩
  ⟨ t ⟩ (σ⟨ σ ⟩ δ , x)
  ≡⟨ sym (law-apply-abs t (σ⟨ σ ⟩ δ) x) ⟩
  apply ((⟨ abs t ⟩ ∘ σ⟨ σ ⟩) δ) x
  ∎
sub-den (app t u) σ δ = begin
  ⟨ app t u / σ ⟩ δ
  ≡⟨⟩
  ⟨ app (t / σ) (u / σ) ⟩ δ
  ≡⟨ law-app (t / σ) (u / σ) δ ⟩
  apply (⟨ t / σ ⟩ δ) (⟨ u / σ ⟩ δ)
  ≡⟨ cong₂ (λ t′ u′ → apply t′ u′) (sub-den t σ δ) (sub-den u σ δ) ⟩
  apply (⟨ t ⟩ (σ⟨ σ ⟩ δ)) (⟨ u ⟩ (σ⟨ σ ⟩ δ))
  ≡⟨ sym (law-app t u (σ⟨ σ ⟩ δ) ) ⟩
  (⟨ app t u ⟩ ∘ σ⟨ σ ⟩) δ
  ∎

