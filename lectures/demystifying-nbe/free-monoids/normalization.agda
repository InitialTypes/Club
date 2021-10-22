{-# OPTIONS --allow-unsolved-metas #-}
module free-monoids.normalization
  (X : Set)
  where

import Relation.Binary.Construct.Always as Total
  renaming (Always to Rel)


open import Relation.Binary.Construct.Closure.Equivalence.Properties
  using    ()
  renaming (a—↠b⇒a↔b to ⟶⋆⇒∼; a—↠b⇒b↔a to ⟶⋆⇒∼˘)

open import Relation.Binary.PropositionalEquality
  using    (_≡_)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂; subst to ≡-subst; isEquivalence to ≡-equiv)

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import free-monoids.model X
open import free-monoids.normal-form X as normal-form
  hiding (Ne; Ne'; Nf; Nf-setoid)
open import free-monoids.theory X as theory
  hiding (Tm; Tm-preorder; Tm-setoid)

private
  Tm          = theory.Tm             [] ∗
  Tm-setoid   = theory.Tm-setoid      [] ∗
  Tm-preorder = theory.Tm-preorder    [] ∗
  Ne          = normal-form.Ne        [] ∗
  Ne'         = normal-form.Ne'       [] ∗
  Nf          = normal-form.Nf        [] ∗
  Nf-setoid   = normal-form.Nf-setoid [] ∗

reify : (n : Nf) → Nf
reify n = n

open Eval' 𝒩𝒻'

norm : (t : Tm) → Nf
norm t = reify ⟦ t ⟧Tm

norm-complete : ∀ {t t' : Tm} → (t⟶⋆t' : t ⟶⋆ t') → norm t ≡ norm t'
norm-complete t⟶⋆t' = ≡-cong reify (⟦⟧Tm-pres-≤ t⟶⋆t')

private
  P : Pred' 𝒯𝓂'
  P = record
    { P                 = λ t → record { Carrier = t ⟶⋆ embNf (norm t) ; _≈_ = _≡_ ; _∼_ = Total.Rel ; isPreorder = isPreorder _ ≡-equiv }
    ; pres-≤˘           = λ t⟶⋆t' t'⟶⋆normt' → ≤-trans[ Tm-preorder ] t⟶⋆t' (≤-trans[ Tm-preorder ] t'⟶⋆normt' (≤-reflexive˘[ Tm-preorder ] (≡-cong embNf (norm-complete t⟶⋆t'))))
    ; pres-++           = λ {xs = t} {ys = u} t⟶⋆normt u⟶⋆normu → ≤-trans[ Tm-preorder ] (⟶⋆-cong-• t⟶⋆normt u⟶⋆normu) (embNf-pres-• (norm t) (norm u))
    ; ≤-cong-pres-++    = λ _ → _
    ; pres-nil          = embNf-pres-e
    ; pres-[]           = embNf-pres-⌜⌝
    ; pres-++-identityˡ = λ _ → _
    ; pres-++-identityʳ = λ _ → _
    ; pres-++-assoc     = λ _ _ → _
    }

norm-adequate′ : ∀ (t : Tm) → t ⟶⋆ embNf (norm t)
norm-adequate′ = fundamental-theorem' P

norm-adequate : ∀ {t u : Tm} → norm t ≡ norm u → t ∼ u
norm-adequate {t} {u} normt≡normu = let open SetoidReasoning Tm-setoid in begin
  t               ≈⟨ ⟶⋆⇒∼ (norm-adequate′ t) ⟩
  embNf (norm t)  ≡⟨ ≡-cong embNf normt≡normu ⟩
  embNf (norm u)  ≈⟨ ⟶⋆⇒∼˘ (norm-adequate′ u) ⟩
  u               ∎
