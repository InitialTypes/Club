open import Library
open import Terms
open import STLC

module Kripke.Semantics where

{- The following is one possible way of encoding Kripke-style models in type
theory, following closely the presentation in "Kripke-Style Models for Typed
Lambda Calculus". Just like in the case of Henkin semantics we are only able to
prove soundness up to functional extensionality. -}


{- The definition of Kripke structures is split up into parts in order to work
around Agda's limitations on recursive definitions inside records. -}

record Kripke′ : Set₁ where
  -- ordered worlds
  field W : Set
  field _◁_ : W → W → Set
  field later-refl : ∀{w} → w ◁ w
  field later-trans : ∀ {w w′ w″} → w ◁ w′ → w′ ◁ w″ → w ◁ w″

  -- semantics of types, indexed by worlds
  field [_] : (A : Type) (w : W) → Set
  field apply : ∀{w A B} → [ A ⇒ B ] w → [ A ] w → [ B ] w

  -- transport
  field _↗_ : ∀{w w′ A} → [ A ] w → w ◁ w′ → [ A ] w′
  field trans-id : ∀{A w} (a : [ A ] w) → a ↗ later-refl ≡ a
  field trans-comp : ∀{A w w′ w″} (p : w ◁ w′) (q : w′ ◁ w″) →
          (a : [ A ] w) → a ↗ later-trans p q ≡ (_↗ q ∘ _↗ p) a

  -- naturality
  field app-nat : ∀{A B w w′} (p : w ◁ w′) (f : [ A ⇒ B ] w) (a : [ A ] w) →
          apply f a ↗ p ≡ apply (f ↗ p) (a ↗ p)

  -- extensionality
  field law-ext : ∀{A B w} (f g : [ A ⇒ B ] w) →
          (∀ {w′} (p : w ◁ w′) a → apply (f ↗ p) a ≡ apply (g ↗ p) a) → f ≡ g

module aux (K : Kripke′) where
  open Kripke′ K
  
  [_]* : (Γ : Context) (w : W) → Set
  [ ε ]* w = ⊤
  [ Γ , A ]* w = [ Γ ]* w × [ A ] w

  v⟨_⟩ : ∀{Γ A} (v : Var Γ A) {w : W} (γ : [ Γ ]* w) → [ A ] w
  v⟨ zero ⟩ = proj₂
  v⟨ suc v ⟩ = v⟨ v ⟩ ∘ proj₁

  _↗*_ : ∀{w w′ Γ} → [ Γ ]* w → w ◁ w′ → [ Γ ]* w′
  _↗*_ {Γ = ε} γ p = tt
  _↗*_ {Γ = Γ , A} (γ , a) p = γ ↗* p , a ↗ p

record Kripke : Set₁ where
  field K′ : Kripke′
  open Kripke′ K′ public
  open aux K′ public

  -- evaluation
  field ⟨_⟩ : ∀{Γ A} (t : Term Γ A) {w} (γ : [ Γ ]* w) → [ A ] w
  field law-var : ∀{Γ A} (v : Var Γ A) {w} (γ : [ Γ ]* w) → ⟨ var v ⟩ γ ≡ v⟨ v ⟩ γ
  field law-app : ∀{Γ A B w} (t : Term Γ (A ⇒ B)) (u : Term Γ A) (γ : [ Γ ]* w) →
          ⟨ app t u ⟩ γ ≡ apply (⟨ t ⟩ γ) (⟨ u ⟩ γ)
  field law-apply-abs : ∀{Γ A B w w′} {p : w ◁ w′}
          (t : Term (Γ , A) B) (γ : [ Γ ]* w) (a : [ A ] w′) →
          apply (⟨ abs t ⟩ γ ↗ p) a ≡ ⟨ t ⟩ (γ ↗* p , a)

module Semantics′ (K : Kripke) where
  open Kripke K public

  sem : STLC-Semantics
  sem = record { _⊨_ = λ Γ A → ∀ w → [ Γ ]* w → [ A ] w ;
                 ⟨_⟩ = λ t w → ⟨ t ⟩ {w} }

  i⟨_⟩ : ∀{Γ Δ} (i : Γ ⊆ Δ) {w} → [ Δ ]* w → [ Γ ]* w
  i⟨_⟩ {ε} i δ = tt
  i⟨_⟩ {Γ , A} i δ = i⟨ i ∘ suc ⟩ δ , v⟨ i zero ⟩ δ

  σ⟨_⟩ : ∀{Γ Δ} (σ : Γ ≤ Δ) {w} → [ Δ ]* w → [ Γ ]* w
  σ⟨_⟩ {ε} σ δ = tt
  σ⟨_⟩ {Γ , A} σ δ = σ⟨ σ ∘ suc  ⟩ δ , ⟨ σ zero ⟩ δ 
 
