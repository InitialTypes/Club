open import Library
open import Terms
open import STLC

module Standard.Semantics where

[_] : (A : Type) → Set
[ atom _ ] = ⊤
[ A ⇒ B ] = [ A ] → [ B ]

[_]* : (Γ : Context) → Set
[ ε ]* = ⊤
[ Γ , A ]* = [ Γ ]* × [ A ]

v⟨_⟩ : ∀{Γ A} (v : Var Γ A) (γ : [ Γ ]*) → [ A ]
v⟨ zero ⟩ = proj₂
v⟨ suc v ⟩ = v⟨ v ⟩ ∘ proj₁

⟨_⟩ : ∀{Γ A} (t : Term Γ A) → (γ : [ Γ ]*) → [ A ]
⟨ var v ⟩ = v⟨ v ⟩
⟨ abs t ⟩ γ = λ a → ⟨ t ⟩ (γ , a)
⟨ app t u ⟩ γ = ⟨ t ⟩ γ (⟨ u ⟩ γ)

sem : STLC-Semantics
sem = record { _⊨_ = λ Γ A → [ Γ ]* → [ A ] ;
               ⟨_⟩ = ⟨_⟩ }

i⟨_⟩ : ∀{Γ Δ} (i : Γ ⊆ Δ) → [ Δ ]* → [ Γ ]*
i⟨_⟩ {ε} i δ = tt
i⟨_⟩ {Γ , A} i δ = i⟨ i ∘ suc ⟩ δ , v⟨ i zero ⟩ δ

σ⟨_⟩ : ∀{Γ Δ} (σ : Γ ≤ Δ) → [ Δ ]* → [ Γ ]*
σ⟨_⟩ {ε} σ δ = tt
σ⟨_⟩ {Γ , A} σ δ = σ⟨ σ ∘ suc  ⟩ δ , ⟨ σ zero ⟩ δ 



{- IPL Stuff -}
module StandardIPL where
  open import IPL
  sem′ : IPL-Semantics
  sem′ = record { _⊨_ = λ Γ A → [ Γ ]* → [ A ] }

  open IPL.IPL-Properties sem′

  is-weekly-sound : weak-soundness
  is-weekly-sound = ⟨_⟩

  is-sound : soundness
  is-sound = ⟨_⟩

  not-complete : weak-completeness → ⊥
  not-complete hyp = peirce-not-IPL (hyp (λ _ → peirces-law))
   where 
    peirces-law : ∀{P Q : Set} → ((P → Q) → P) → P
    peirces-law = {!!} -- not provable, but consistent
    peirce-not-IPL : (∀{A B : Type} → Term ε (((A ⇒ B) ⇒ A) ⇒ A)) → ⊥
    peirce-not-IPL = {!!} -- can be shown using Kripke models
