open import Terms
open import IPL

open import Data.Unit using (⊤)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong)

module PreHenkin.Structure where

{- This file contains a definition of "Pre-Henkin structures", that are untyped
henkin structures. The result is a notion of model of IPL that is sound but not
(strongly) complete. The laws needed for propositional soundness turn out to
correspond to logical predicates.

I haven't got around to cleaning this up yet. Please excuse the mess. -}

{- subsets -}
𝓟 : Set → Set₁
𝓟 D = Σ Set (λ D′ → D′ → D)

set : ∀{D} → 𝓟 D → Set
set = proj₁

inj : ∀{D} (D′ : 𝓟 D) → (set D′ → D)
inj = proj₂

_∈_ : ∀{D} → (x : D) (D′ : 𝓟 D) → Set
x ∈ D′ = Σ (set D′) (λ |x| → inj D′ |x| ≡ x)

--underlying element
el : ∀{D D′} {x : D} → x ∈ D′ → set D′
el = proj₁

-- witness of containment
wtn : ∀{D D′} {x : D} → (x∈D′ : x ∈ D′) → inj D′ (el x∈D′) ≡ x
wtn = proj₂



module star (D : Set) where
  D^ : (Γ : Context) → Set
  D^ ε = ⊤
  D^ (Γ , A) = D^ Γ × D

  v⟨_⟩ : ∀{Γ A} (v : Var Γ A) (γ : D^ Γ) → D
  v⟨ zero ⟩ = proj₂
  v⟨ suc v ⟩ = v⟨ v ⟩ ∘ proj₁


record PreHenkinStructure : Set₁ where
  field D : Set
  open star D public
  field
    ⟨_⟩ : ∀{Γ A} → (t : Term Γ A) (γ : D^ Γ) → D
    apply : D → D → D
    law-var : ∀{Γ A} (v : Var Γ A) γ → ⟨ var v ⟩ γ ≡ v⟨ v ⟩ γ
    law-apply-abs : ∀{Γ A B} (t : Term (Γ , A) B) (γ : D^ Γ) (a : D) →
      apply (⟨ abs t ⟩ γ) a ≡ ⟨ t ⟩ (γ , a)
    law-app : ∀{Γ A B} (t : Term Γ (A ⇒ B)) (u : Term Γ A) (γ : D^ Γ) →
      ⟨ app t u ⟩ γ ≡ apply (⟨ t ⟩ γ) (⟨ u ⟩ γ)
  field -- typing
    [_] : (A : Type) → 𝓟 D
    law-apply-typed : ∀{A B f} → f ∈ [ A ⇒ B ] → ∀ a → a ∈ [ A ] → apply f a ∈ [ B ]
    law-logical : ∀{A B f} → (∀ a → a ∈ [ A ] → apply f a ∈ [ B ]) → f ∈ [ A ⇒ B ]

module []* (P : PreHenkinStructure) where
  open PreHenkinStructure P

  [_]* : (Γ : Context) → 𝓟 (D^ Γ)
  [ ε ]* = ⊤ , λ tt → tt
  [ Γ , A ]* = (set [ Γ ]* × set [ A ]) , λ { (γ , a) → inj [ Γ ]* γ , inj [ A ] a}

  v⟨⟩-welltyped : ∀{Γ A} (v : Var Γ A) {γ} → (γ ∈ [ Γ ]*) → v⟨ v ⟩ γ ∈ [ A ]
  v⟨⟩-welltyped zero γ∈[Γ]* = proj₂ (el γ∈[Γ]*) , cong proj₂ (wtn γ∈[Γ]*) 
  v⟨⟩-welltyped (suc v) γ∈[Γ]* = v⟨⟩-welltyped v (proj₁ (el γ∈[Γ]*) , cong proj₁ (wtn γ∈[Γ]*))
