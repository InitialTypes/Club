open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Product using (Σ-syntax; _,_) renaming (proj₁ to fst; proj₂ to snd)

open import Function using (id)

open import Level using (zero; suc)

open import Relation.Nullary using (¬_; yes; no)

open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong-app; module ≡-Reasoning)

module Exercises.Awodey.Chap06.Ex14
  -- reflexive domain
  (D    : Set)
  (s    : (f : D → D) → D)
  (r    : (x : D) → (D → D))
  (eq-1 : ∀ (x : D)     → s (r x) ≡ x)
  (eq-2 : ∀ (f : D → D) → r (s f) ≡ f)
  where

private
  impossible : {A B : Set} → (a : A) → (¬a : ¬ A) → B
  impossible a ¬a = ⊥-elim (¬a a)

  trans' : ∀ {A : Set} {x y y' : A} → x ≡ y → x ≡ y' → y ≡ y'
  trans' x≡y x≡y' = trans (sym x≡y) x≡y'

  r-inj : ∀ {x y : D} → r x ≡ r y → x ≡ y
  r-inj {x} {y} rx≡ry = let open ≡-Reasoning in begin
    x        ≡˘⟨ eq-1 x ⟩
    s (r x)  ≡⟨ cong s rx≡ry ⟩
    s (r y)  ≡⟨ eq-1 y ⟩
    y        ∎

  r-surj : ∀ (f : D → D) → Σ[ x ∈ D ] r x ≡ f
  r-surj f = s f , eq-2 f

inh : D
inh = {!!}

private
  d₀ = inh

module _ (≡-dec : Decidable (_≡_ {A = D})) where
  private
    _≡?_ = ≡-dec

  subsingl : ∀ (x x' : D) → x ≡ x'
  subsingl x x' = {!!}

  singl : Σ[ x ∈ D ] ∀ (x' : D) → x' ≡ x
  singl = d₀ , λ x' → subsingl x' d₀

  -- note that any two singletons, in particular any two reflexive
  -- domains (with decidable equality), are isomorphic
