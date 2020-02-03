module classical-proofs-as-programs where

open import Relation.Binary.PropositionalEquality as Eq

open        Eq               using (_≡_; refl)
open import Data.Sum         using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Data.Nat         using (ℕ; _<_; _≤_; z≤n; s≤s)
open import Data.Product     using (Σ; _,_; proj₁)

Σ-syntax ∃-syntax : {A : Set} → (φ : A → Set) → Set

Σ-syntax = λ φ → Σ _ φ
∃-syntax = λ φ → ¬ ∀ x → ¬ φ x

syntax Σ-syntax (λ x → φ) = Σ[ x ] φ
syntax ∃-syntax (λ x → φ) = ∃[ x ] φ

module Top {A} (ψ : A → Set) where

  -- φ := Σ[ x ](ψ x)
  ¬φ_ : Set → Set
  ¬φ ϑ = ϑ → Σ[ x ](ψ x)

  top : ¬φ Σ[ x ](¬φ ¬φ (ψ x))
  top (n , imp) = imp (λ x → n , x)

module Example where

  open Top (λ x → 0 < x)

  -- A := ⊥ checks out.
  thm₀ : ¬ ¬ Σ[ x ](¬ ¬ (0 < x))
  thm₀ = λ ne → ne (0 , λ nz → ne (1 , λ x → x (s≤s z≤n)))

  -- But thm₀ works for ⊥ replaced with _any_ φ.
  -- Notice that the proof term is unchanged.
  thm₁ : ∀ {φ : Set} → (Σ[ x ](((0 < x) → φ) → φ) → φ) → φ
  thm₁ = λ ne → ne (0 , λ nz → ne (1 , λ x → x (s≤s z≤n)))

  -- We reconstruct the constructive proof from the translation as follows.
  thm : Σ[ x ](0 < x)
  thm = thm₁ {φ = Σ[ x ](0 < x)} top

  _ : proj₁ thm ≡ 1
  _ = refl
