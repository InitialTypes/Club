open import Terms
open import STLC

open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl; sym; cong; cong₂; cong-app; module ≡-Reasoning; Extensionality)
open import Data.Product

open import Function using (_∘_; id)
open ≡-Reasoning

module Kripke.Kripke where

postulate W : Set
postulate _◁_ : W → W → Set
postulate later-refl : ∀{w} → w ◁ w
postulate later-trans : ∀ {w w′ w″} → w ◁ w′ → w′ ◁ w″ → w ◁ w″
-- postulate later-antisym : ∀ {w w′} → w ◁ w′ → w′ ◁ w → w ≡ w′

postulate [_] : (A : Type) (w : W) → Set
postulate apply : ∀{w A B} → [ A ⇒ B ] w → [ A ] w → [ B ] w
-- transport
postulate _↗_ : ∀{w w′ A} → [ A ] w → w ◁ w′ → [ A ] w′

-- functor laws (pointwise)
postulate trans-id : ∀{A w} (a : [ A ] w) → a ↗ later-refl ≡ a
postulate trans-comp : ∀{A w w′ w″} (p : w ◁ w′) (q : w′ ◁ w″) →
            (a : [ A ] w) → a ↗ later-trans p q ≡ (_↗ q ∘ _↗ p) a

-- naturality
postulate app-nat : ∀{A B w w′} (p : w ◁ w′) (f : [ A ⇒ B ] w) (a : [ A ] w) →
            apply f a ↗ p ≡ apply (f ↗ p) (a ↗ p)

postulate law-ext : ∀{A B w} (f g : [ A ⇒ B ] w) →
            (∀ {w′} (p : w ◁ w′) a → apply (f ↗ p) a ≡ apply (g ↗ p) a) → f ≡ g

-- environment
[_]* : (Γ : Context) (w : W) → Set
[ ε ]* w = ⊤
[ Γ , A ]* w = [ Γ ]* w × [ A ] w

proj : ∀{Γ A} (t : Var Γ A) {w : W} (γ : [ Γ ]* w) → [ A ] w
proj zero = proj₂
proj (suc t) = proj t ∘ proj₁

-- transporting environments
_↗*_ : ∀{w w′ Γ} → [ Γ ]* w → w ◁ w′ → [ Γ ]* w′
_↗*_ {Γ = ε} γ p = ⊤.tt
_↗*_ {Γ = Γ , A} (γ , a) p = γ ↗* p , a ↗ p

trans*-id : ∀{Γ w} (γ : [ Γ ]* w) → γ ↗* later-refl ≡ γ
trans*-id {ε} γ = refl
trans*-id {Γ , A} (γ , a) = begin
  (γ , a) ↗* later-refl
  ≡⟨⟩
  γ ↗* later-refl , a ↗ later-refl
  ≡⟨ cong₂ _,_ (trans*-id γ) (trans-id a) ⟩
  (γ , a)
  ∎

-- evaluation
postulate ⟨_⟩ : ∀{Γ A} (t : Term Γ A) {w} (γ : [ Γ ]* w) → [ A ] w
postulate law-var : ∀{Γ A} (v : Var Γ A) {w} (γ : [ Γ ]* w) → ⟨ var v ⟩ γ ≡ proj v γ
postulate law-app : ∀{Γ A B w} (t : Term Γ (A ⇒ B)) (u : Term Γ A) (γ : [ Γ ]* w) →
            ⟨ app t u ⟩ γ ≡ apply (⟨ t ⟩ γ) (⟨ u ⟩ γ)
postulate law-apply-abs : ∀{Γ A B w w′} {p : w ◁ w′}
            (t : Term (Γ , A) B) (γ : [ Γ ]* w) (a : [ A ] w′) →
            apply (⟨ abs t ⟩ γ ↗ p) a ≡ ⟨ t ⟩ (γ ↗* p , a)

kripke-sem : STLC-Semantics
kripke-sem = record { _⊨_ = λ Γ A → ∀ {w} → [ Γ ]* w → [ A ] w ;
                      ⟨_⟩ = ⟨_⟩ }

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
  proj v (γ ↗* p) ≡ (proj v γ ↗ p)
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

-- Weakenings, Substitutions, Substitution Lemma
i⟨_⟩ : ∀{Γ Δ} (i : Γ ⊆ Δ) {w} → [ Δ ]* w → [ Γ ]* w
i⟨_⟩ {ε} i δ = ⊤.tt
i⟨_⟩ {Γ , A} i δ = i⟨ i ∘ suc ⟩ δ , proj (i zero) δ

weakv-den : ∀{Γ A Δ w}(v : Var Γ A)(i : Γ ⊆ Δ) →
  proj (i v) {w} ≡ proj v ∘ i⟨ i ⟩
weakv-den zero i = refl
weakv-den (suc v) i = weakv-den v (i ∘ suc)

weak-den-comp : ∀{Γ Δ Ω w} (i : Δ ⊆ Ω) (i′ : Γ ⊆ Δ) →
  i⟨ i ∘ i′ ⟩ {w} ≡ i⟨ i′ ⟩ ∘ i⟨ i ⟩
weak-den-comp {ε} i i′ = refl
weak-den-comp {Γ , A} i i′ = begin
  i⟨ i ∘ i′ ⟩
  ≡⟨⟩
  (λ δ → i⟨ i ∘ i′ ∘ suc ⟩ δ , proj ((i ∘ i′) zero) δ)
  ≡⟨ cong (λ f δ → f δ , proj ((i ∘ i′) zero) δ) (weak-den-comp i (i′ ∘ suc)) ⟩
  (λ δ → i⟨ i′ ∘ suc ⟩ (i⟨ i ⟩ δ) , proj ((i ∘ i′) zero) δ)
  ≡⟨ cong (λ x δ → (i⟨ i′ ∘ suc ⟩ (i⟨ i ⟩ δ)) , (x δ)) (weakv-den (i′ zero) i)⟩
  (λ δ → i⟨ i′ ∘ suc ⟩ (i⟨ i ⟩ δ) , proj (i′ zero) (i⟨ i ⟩ δ))
  ≡⟨⟩
  i⟨ i′ ⟩ ∘ i⟨ i ⟩
  ∎

lift-weak-den : ∀{Γ Δ B w} → (i : Γ ⊆ Δ) → i⟨ suc {B = B} ∘ i ⟩ {w} ≡ i⟨ i ⟩ ∘ proj₁
lift-weak-den {ε} i = refl
lift-weak-den {Γ , A} {Δ} {B} i = begin
  i⟨ suc ∘ i ⟩
  ≡⟨⟩
  (λ δ → i⟨ suc ∘ i ∘ suc ⟩ δ , proj (i zero) (proj₁ δ))
  ≡⟨ cong (λ x δ → (x δ) , (proj (i zero) (proj₁ δ))) (lift-weak-den {B = B} (i ∘ suc)) ⟩
  (λ δ → i⟨ i ∘ suc ⟩ (proj₁ δ) , proj (i zero) (proj₁ δ))
  ≡⟨⟩
  i⟨ i ⟩ ∘ proj₁
  ∎

id-weak-den : ∀{Γ w} → i⟨ (λ {A} (v : Var Γ A) → v) ⟩ {w} ≡ id
id-weak-den {ε} = refl
id-weak-den {Γ , A} {w} rewrite lift-weak-den {Γ} {Γ} {A} {w} id |
                        id-weak-den {Γ} {w} = refl

proj-trans : ∀{Γ A} (v : Var Γ A) {w} (γ : [ Γ ]* w) {w′} (p : w ◁ w′) →
  proj v γ ↗ p ≡ proj v (γ ↗* p)
proj-trans zero γ p = refl
proj-trans (suc v) (γ , a) p rewrite proj-trans v γ p = refl

weak-trans : ∀{Γ Δ} (i : Γ ⊆ Δ) {w} (δ : [ Δ ]* w) {w′} (p : w ◁ w′) →
  i⟨ i ⟩ δ ↗* p ≡ i⟨ i ⟩ (δ ↗* p)
weak-trans {ε} {Δ} i {w} δ {w′} p = refl
weak-trans {Γ , A} {Δ} i {w} δ {w′} p = begin
  i⟨ i ∘ suc ⟩ δ ↗* p , proj (i zero) δ ↗ p
  ≡⟨ cong₂ _,_ (weak-trans (i ∘ suc) δ p) (proj-trans (i zero) δ p) ⟩
  i⟨ i ∘ suc ⟩ (δ ↗* p) , proj (i zero) (δ ↗* p)
  ∎

-- only up to extensionality
weak-den : ∀{Γ A Δ} (t : Term Γ A) (i : Γ ⊆ Δ) {w} →
  (δ : [ Δ ]* w) → ⟨ t ↓ i ⟩ δ ≡ (⟨ t ⟩ ∘ i⟨ i ⟩) δ
weak-den (var v) i δ = begin
  ⟨ var v ↓ i ⟩ δ
  ≡⟨ law-var (i v) δ ⟩
  proj (i v) δ
  ≡⟨ cong-app (weakv-den v i) δ ⟩
  proj v (i⟨ i ⟩ δ)
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

σ⟨_⟩ : ∀{Γ Δ} (σ : Γ ≤ Δ) {w} → [ Δ ]* w → [ Γ ]* w
σ⟨_⟩ {ε} σ δ = ⊤.tt
σ⟨_⟩ {Γ , A} σ δ = σ⟨ σ ∘ suc  ⟩ δ , ⟨ σ zero ⟩ δ 
  
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
  ⟨ σ v ⟩ {w} ≡ proj v ∘ σ⟨ σ ⟩
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
  (proj v ∘ σ⟨ σ ⟩) δ
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

open STLC-Semantics kripke-sem hiding (⟨_⟩)
open βη-Equality
is-strongly-stlc-sound′ : ∀{Γ A} {𝓐 : Axioms} {t t′ : Term Γ A} →
  𝓐 ⊢ t ≡λ t′ → (⊨ 𝓐) → ∀ {w} (γ : [ Γ ]* w) → ⟨ t ⟩ γ ≡ ⟨ t′ ⟩ γ
is-strongly-stlc-sound′ (axiom t u i x) hyp γ = begin
  ⟨ t ↓ i ⟩ γ
  ≡⟨ weak-den t i γ ⟩
  ⟨ t ⟩ (i⟨ i ⟩ γ)
  ≡⟨ cong (λ t′ → t′ ⊤.tt) (hyp x) ⟩
  ⟨ u ⟩ (i⟨ i ⟩ γ)
  ≡⟨ sym (weak-den u i γ) ⟩
  ⟨ u ↓ i ⟩ γ
  ∎
is-strongly-stlc-sound′ (β t u) hyp γ = begin
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
is-strongly-stlc-sound′ (η t) hyp γ = law-ext (⟨ t ⟩ γ)
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
is-strongly-stlc-sound′ (λcong-abs {t = t} {t′ = t′} eq) hyp γ =
  law-ext (⟨ abs t ⟩ γ) (⟨ abs t′ ⟩ γ) λ p a → begin
  apply (⟨ abs t ⟩ γ ↗ p) a
  ≡⟨ law-apply-abs t γ a ⟩
  ⟨ t ⟩ (γ ↗* p , a)
  ≡⟨ is-strongly-stlc-sound′ eq hyp (γ ↗* p , a) ⟩
  ⟨ t′ ⟩ (γ ↗* p , a)
  ≡⟨ sym (law-apply-abs t′ γ a) ⟩
  apply (⟨ abs t′ ⟩ γ ↗ p) a
  ∎
is-strongly-stlc-sound′ (λcong-app {Γ} {A} {B} {t} {t′} {u} {u′} eq eq₁) hyp γ = begin
  ⟨ app t u ⟩ γ
  ≡⟨ law-app t u γ ⟩
  apply (⟨ t ⟩ γ) (⟨ u ⟩ γ)
  ≡⟨ cong₂ apply (is-strongly-stlc-sound′ eq hyp γ) (is-strongly-stlc-sound′ eq₁ hyp γ) ⟩
  apply (⟨ t′ ⟩ γ) (⟨ u′ ⟩ γ)
  ≡⟨ sym (law-app t′ u′ γ) ⟩
  ⟨ app t′ u′ ⟩ γ
  ∎
is-strongly-stlc-sound′ λrefl hyp γ = refl
is-strongly-stlc-sound′ (λsym eq) hyp γ = sym (is-strongly-stlc-sound′ eq hyp γ)
is-strongly-stlc-sound′ (λtrans {Γ} {A} {t} {t′} {t″} eq eq₁) hyp γ = begin
  ⟨ t ⟩ γ
  ≡⟨ is-strongly-stlc-sound′ eq hyp γ ⟩
  ⟨ t′ ⟩ γ
  ≡⟨ is-strongly-stlc-sound′ eq₁ hyp γ ⟩
  ⟨ t″ ⟩ γ
  ∎
