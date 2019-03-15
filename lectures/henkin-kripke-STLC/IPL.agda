open import Library
open import Terms

module IPL where

record IPL-Semantics : Set₁ where
  field _⊨_ : (Γ : Context) (A : Type) → Set


module IPL-Properties (sem : IPL-Semantics) where
  open IPL-Semantics sem

  weak-soundness : Set
  weak-soundness = ∀{A} → Term ε A → ε ⊨ A

  weak-completeness : Set
  weak-completeness = ∀{A} → ε ⊨ A → Term ε A

  soundness : Set
  soundness = ∀{Γ A} → Term Γ A → Γ ⊨ A

  completeness : Set
  completeness = ∀{Γ A} → Γ ⊨ A → Term Γ A


record IPL-Model : Set₁ where
  field sem : IPL-Semantics
  field is-sound : IPL-Properties.soundness sem
