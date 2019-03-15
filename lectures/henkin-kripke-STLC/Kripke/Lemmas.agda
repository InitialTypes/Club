open import Library
open import Terms
open import STLC

open import Kripke.Semantics

module Kripke.Lemmas (K : Kripke) where
open Semantics′ K
open ≡-Reasoning

trans*-id : ∀{Γ w} (γ : [ Γ ]* w) → γ ↗* later-refl ≡ γ
trans*-id {ε} γ = refl
trans*-id {Γ , A} (γ , a) = begin
  (γ , a) ↗* later-refl
  ≡⟨⟩
  γ ↗* later-refl , a ↗ later-refl
  ≡⟨ cong₂ _,_ (trans*-id γ) (trans-id a) ⟩
  (γ , a)
  ∎

trans*-comp : ∀{Γ w w′ w″} (p : w ◁ w′) (q : w′ ◁ w″) →
            (γ : [ Γ ]* w) → γ ↗* later-trans p q ≡ (γ ↗* p) ↗* q
trans*-comp {ε} {w} {w′} {w″} p q γ = refl
trans*-comp {Γ , A} {w} {w′} {w″} p q (γ , a) = begin
  (γ ↗* later-trans p q) , (a ↗ later-trans p q)
  ≡⟨ cong₂ _,_ (trans*-comp p q γ) (trans-comp p q a) ⟩
  ((γ ↗* p) ↗* q) , ((a ↗ p) ↗ q)
  ∎

-- the transport lemma
transv-den : ∀{Γ A} (v : Var Γ A) {w w′} γ (p : w ◁ w′) →
  v⟨ v ⟩ (γ ↗* p) ≡ (v⟨ v ⟩ γ ↗ p)
transv-den zero γ p = refl
transv-den (suc v) (γ , a) p = transv-den v γ p

trans-den : ∀{Γ A} (t : Term Γ A) {w w′} γ (p : w ◁ w′) →
  ⟨ t ⟩ (γ ↗* p) ≡ ⟨ t ⟩ γ ↗ p
trans-den (var v) γ p rewrite law-var v γ | law-var v (γ ↗* p) = transv-den v γ p
trans-den (abs {Γ} {A} {B} t) γ p = law-ext (⟨ abs t ⟩ (γ ↗* p))
                                       (⟨ abs t ⟩ γ ↗ p)
                                       λ p′ a → begin
  apply (⟨ abs t ⟩ (γ ↗* p) ↗ p′) a
  ≡⟨ law-apply-abs t (γ ↗* p) a ⟩
  ⟨ t ⟩ ((γ ↗* p) ↗* p′ , a)
  ≡⟨ cong (λ γ′ → ⟨ t ⟩ (γ′ , a)) (sym (trans*-comp p p′ γ)) ⟩
  ⟨ t ⟩ (γ ↗* (later-trans p p′) , a)
  ≡⟨ sym (law-apply-abs t γ a) ⟩
  apply (⟨ abs t ⟩ γ ↗ (later-trans p p′)) a
  ≡⟨ cong (λ t → apply t a) (trans-comp p p′ (⟨ abs t ⟩ γ)) ⟩
  apply ((⟨ abs t ⟩ γ ↗ p) ↗ p′) a
  ∎
trans-den (app t u) γ p = begin
  ⟨ app t u ⟩ (γ ↗* p)
  ≡⟨ law-app t u (γ ↗* p) ⟩
  apply (⟨ t ⟩ (γ ↗* p)) (⟨ u ⟩ (γ ↗* p))
  ≡⟨ cong₂ apply (trans-den t γ p) (trans-den u γ p) ⟩
  apply (⟨ t ⟩ γ ↗ p) (⟨ u ⟩ γ ↗ p)
  ≡⟨ sym (app-nat p (⟨ t ⟩ γ) (⟨ u ⟩ γ)) ⟩
  (apply (⟨ t ⟩ γ) (⟨ u ⟩ γ) ↗ p)
  ≡⟨ sym (cong (_↗ p) (law-app t u γ)) ⟩
  ⟨ app t u ⟩ γ ↗ p
  ∎

weakv-den : ∀{Γ A Δ w}(v : Var Γ A)(i : Γ ⊆ Δ) →
  v⟨ i v ⟩ {w} ≡ v⟨ v ⟩ ∘ i⟨ i ⟩
weakv-den zero i = refl
weakv-den (suc v) i = weakv-den v (i ∘ suc)

weak-den-comp : ∀{Γ Δ Ω w} (i : Δ ⊆ Ω) (i′ : Γ ⊆ Δ) →
  i⟨ i ∘ i′ ⟩ {w} ≡ i⟨ i′ ⟩ ∘ i⟨ i ⟩
weak-den-comp {ε} i i′ = refl
weak-den-comp {Γ , A} i i′ = begin
  i⟨ i ∘ i′ ⟩
  ≡⟨⟩
  (λ δ → i⟨ i ∘ i′ ∘ suc ⟩ δ , v⟨ (i ∘ i′) zero ⟩ δ)
  ≡⟨ cong (λ f δ → f δ , v⟨ (i ∘ i′) zero ⟩ δ) (weak-den-comp i (i′ ∘ suc)) ⟩
  (λ δ → i⟨ i′ ∘ suc ⟩ (i⟨ i ⟩ δ) , v⟨ (i ∘ i′) zero ⟩ δ)
  ≡⟨ cong (λ x δ → (i⟨ i′ ∘ suc ⟩ (i⟨ i ⟩ δ)) , (x δ)) (weakv-den (i′ zero) i)⟩
  (λ δ → i⟨ i′ ∘ suc ⟩ (i⟨ i ⟩ δ) , v⟨ i′ zero ⟩ (i⟨ i ⟩ δ))
  ≡⟨⟩
  i⟨ i′ ⟩ ∘ i⟨ i ⟩
  ∎

lift-weak-den : ∀{Γ Δ B w} → (i : Γ ⊆ Δ) → i⟨ suc {B = B} ∘ i ⟩ {w} ≡ i⟨ i ⟩ ∘ proj₁
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

id-weak-den : ∀{Γ w} → i⟨ (λ {A} (v : Var Γ A) → v) ⟩ {w} ≡ id
id-weak-den {ε} = refl
id-weak-den {Γ , A} {w} rewrite lift-weak-den {Γ} {Γ} {A} {w} id |
                        id-weak-den {Γ} {w} = refl

proj-trans : ∀{Γ A} (v : Var Γ A) {w} (γ : [ Γ ]* w) {w′} (p : w ◁ w′) →
  v⟨ v ⟩ γ ↗ p ≡ v⟨ v ⟩ (γ ↗* p)
proj-trans zero γ p = refl
proj-trans (suc v) (γ , a) p rewrite proj-trans v γ p = refl

weak-trans : ∀{Γ Δ} (i : Γ ⊆ Δ) {w} (δ : [ Δ ]* w) {w′} (p : w ◁ w′) →
  i⟨ i ⟩ δ ↗* p ≡ i⟨ i ⟩ (δ ↗* p)
weak-trans {ε} {Δ} i {w} δ {w′} p = refl
weak-trans {Γ , A} {Δ} i {w} δ {w′} p = begin
  i⟨ i ∘ suc ⟩ δ ↗* p , v⟨ i zero ⟩ δ ↗ p
  ≡⟨ cong₂ _,_ (weak-trans (i ∘ suc) δ p) (proj-trans (i zero) δ p) ⟩
  i⟨ i ∘ suc ⟩ (δ ↗* p) , v⟨ i zero ⟩ (δ ↗* p)
  ∎

-- only up to extensionality
weak-den : ∀{Γ A Δ} (t : Term Γ A) (i : Γ ⊆ Δ) {w} →
  (δ : [ Δ ]* w) → ⟨ t ↓ i ⟩ δ ≡ (⟨ t ⟩ ∘ i⟨ i ⟩) δ
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
                                       (λ p a → begin
  apply (⟨ abs (t ↓ ↑⊆ i) ⟩ δ ↗ p) a
  ≡⟨ law-apply-abs (t ↓ ↑⊆ i) δ a ⟩
  ⟨ t ↓ ↑⊆ i ⟩ (δ ↗* p , a)
  ≡⟨ weak-den t (↑⊆ i) ((δ ↗* p) , a) ⟩
  ⟨ t ⟩ (i⟨ ↑⊆ i ⟩ (δ ↗* p , a))
  ≡⟨ cong (λ i  → ⟨ t ⟩ (i (δ ↗* p , a) , a)) (lift-weak-den i) ⟩
  ⟨ t ⟩ (i⟨ i ⟩ (δ ↗* p) , a)
  ≡⟨ cong (λ i → ⟨ t ⟩ (i , a)) (sym (weak-trans i δ p)) ⟩
  ⟨ t ⟩ (i⟨ i ⟩ δ ↗* p , a)
  ≡⟨ sym (law-apply-abs t (i⟨ i ⟩ δ) a) ⟩
  apply (⟨ abs t ⟩ (i⟨ i ⟩ δ) ↗ p) a
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

sub-weaken : ∀{Γ Δ w} (i : Γ ⊆ Δ) →
  (δ : [ Δ ]* w) → σ⟨ var ∘ i ⟩ δ ≡ i⟨ i ⟩ δ
sub-weaken {ε} i δ = refl
sub-weaken {Γ , A} i δ = begin
  σ⟨ var ∘ i ⟩ δ
  ≡⟨⟩
  σ⟨ var ∘ i ∘ suc ⟩ δ , ⟨ var (i zero) ⟩ δ
  ≡⟨ cong₂ _,_ (sub-weaken (i ∘ suc) δ) (law-var (i zero) δ) ⟩
  i⟨ i ⟩ δ
  ∎

-- only up to extensionality
weakσ-den : ∀{Γ Δ Ω w} (σ : Γ ≤ Δ) (i : Δ ⊆ Ω) →
  (ω : [ Ω ]* w) → σ⟨ (λ v → σ v ↓ i) ⟩ ω ≡ σ⟨ σ ⟩ (i⟨ i ⟩ ω)
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

subv-den : ∀{Γ A Δ w}(v : Var Γ A)(σ : Γ ≤ Δ) →
  ⟨ σ v ⟩ {w} ≡ v⟨ v ⟩ ∘ σ⟨ σ ⟩
subv-den zero i = refl
subv-den (suc v) i = subv-den v (i ∘ suc)

sub-trans : ∀{Γ Δ} (σ : Γ ≤ Δ) {w} (δ : [ Δ ]* w) {w′} (p : w ◁ w′) →
  σ⟨ σ ⟩ δ ↗* p ≡ σ⟨ σ ⟩ (δ ↗* p)
sub-trans {ε} {Δ} σ {w} δ {w′} p = refl
sub-trans {Γ , A} {Δ} σ {w} δ {w′} p = begin
  σ⟨ σ ∘ suc ⟩ δ ↗* p , ⟨ σ zero ⟩ δ ↗ p
  ≡⟨ cong₂ _,_ (sub-trans (σ ∘ suc) δ p) (sym (trans-den (σ zero) δ p)) ⟩
  σ⟨ σ ∘ suc ⟩ (δ ↗* p) , ⟨ σ zero ⟩ (δ ↗* p)
  ∎

-- the substitution lemma
  -- only up to extensionality
sub-den : ∀{Γ A Δ w}(t : Term Γ A)(σ : Γ ≤ Δ) →
  (δ : [ Δ ]* w) → ⟨ t / σ ⟩ δ ≡ (⟨ t ⟩ ∘ σ⟨ σ ⟩) δ
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
            λ p a → begin
  apply (⟨ abs (t / ↑σ σ) ⟩ δ ↗ p) a
  ≡⟨ law-apply-abs (t / ↑σ σ) δ a ⟩
  ⟨ t / ↑σ σ ⟩ (δ ↗* p , a)
  ≡⟨ sub-den t (↑σ σ) (δ ↗* p , a) ⟩
  ⟨ t ⟩ (σ⟨ ↑σ σ ⟩ (δ ↗* p , a))
  ≡⟨ cong (λ y → ⟨ t ⟩ (y , ⟨ var zero ⟩ (δ ↗* p , a))) (weakσ-den σ suc (δ ↗* p , a)) ⟩
  ⟨ t ⟩ (σ⟨ σ ⟩ (i⟨ suc ⟩ (δ ↗* p , a)) , ⟨ var zero ⟩ (δ ↗* p , a))
  ≡⟨ cong (λ y → ⟨ t ⟩ (σ⟨ σ ⟩ (y (δ ↗* p , a)) , ⟨ var zero ⟩ (δ ↗* p , a))) (lift-weak-den id) ⟩
  ⟨ t ⟩ (σ⟨ σ ⟩ (i⟨ id ⟩ (δ ↗* p)) , ⟨ var zero ⟩ (δ ↗* p , a))
  ≡⟨ cong (λ y → ⟨ t ⟩ (σ⟨ σ ⟩ (y (δ ↗* p)) , ⟨ var zero ⟩ (δ ↗* p , a))) id-weak-den ⟩
  ⟨ t ⟩ (σ⟨ σ ⟩ (δ ↗* p) , ⟨ var zero ⟩ (δ ↗* p , a))
  ≡⟨ cong (λ y → ⟨ t ⟩ (σ⟨ σ ⟩ (δ ↗* p) , y)) (law-var zero (δ ↗* p , a)) ⟩
  ⟨ t ⟩ (σ⟨ σ ⟩ (δ ↗* p) , a)
  ≡⟨ cong (λ δ′ → ⟨ t ⟩ (δ′ , a)) (sym (sub-trans σ δ p)) ⟩
  ⟨ t ⟩ (σ⟨ σ ⟩ δ ↗* p , a)
  ≡⟨ sym (law-apply-abs t (σ⟨ σ ⟩ δ) a) ⟩
  apply (⟨ abs t ⟩ (σ⟨ σ ⟩ δ) ↗ p) a
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
