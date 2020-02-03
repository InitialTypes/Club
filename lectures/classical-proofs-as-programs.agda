module classical-proofs-as-programs where

open import Relation.Binary.PropositionalEquality as Eq

open        Eq               using (_≡_; refl)
open import Data.Sum         using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Data.Nat         using (ℕ; _<_; _≤_)
open import Data.Product     using (∃-syntax; _,_; proj₁)

module Top {A} (ψ : A → Set) where

   -- φ := ∃[ x ](ψ x)
  ¬φ_ : Set → Set
  ¬φ ϑ = ϑ → ∃[ x ](ψ x)

  top : ¬φ ∃[ x ](¬φ ¬φ (ψ x))
  top (n , imp) = imp (λ x → n , x)

module Example where

  open Top (λ x → 0 < x)

  -- A := ⊥ checks out.
  thm₀ : ¬ ¬ ∃[ x ](¬ ¬ (0 < x))
  thm₀ = λ ne → ne (0 , λ nz → ne (1 , λ x → x (_≤_.s≤s _≤_.z≤n)))

  -- But thm₀ works for ⊥ replaced with _any_ A.
  -- Notice that the proof term is unchanged.
  thm₁ : ∀ (A : Set) → ((∃[ x ](((0 < x) → A) → A)) → A) → A
  thm₁ _ = λ ne → ne (0 , λ nz → ne (1 , λ x → x (_≤_.s≤s _≤_.z≤n)))

  -- We reconstruct the constructive proof from the translation as follows.
  thm : ∃[ x ](0 < x)
  thm = thm₁ (∃[ x ](0 < x)) top

  _ : proj₁ thm ≡ 1
  _ = refl
