-- Exercise:  A¹ ≅ A

open import Relation.Binary using (Setoid; IsEquivalence); open Setoid; open IsEquivalence
import Relation.Binary.Reasoning.Setoid as EqR

open import CCC as _  -- Import the contents, hide the module itself

module Exercises.AToTheOneIsomorphicA {o m e} (C : CCC o m e) (let open CCC C) where

  -- Show that  Arr Unit A ≅ A

  -- to : A¹ → A   (just apply to unit)

  to : ∀{a} → Hom (Arr Unit a) a
  to {a} = comp apply (pair (id   (Arr Unit a))
                            (unit (Arr Unit a)))

  -- from : A → A¹  (λ a _ → a)

  from : ∀{a} → Hom a (Arr Unit a)
  from {a} = curry π₁

  -- to ∘ from = id

  to-from : ∀{a} → Eq (comp to from) (id a)
  to-from {a} = begin
    comp to from                                                             ≡⟨⟩
    comp (comp apply (pair (id _) (unit _))) (curry π₁)                      ≈⟨ assoc _ _ _ ⟩
    comp apply (comp (pair (id _) (unit _)) (curry π₁))                      ≈⟨ comp-cong eq-refl (pair-nat _ _ _) ⟩
    comp apply (pair (comp (id _) (curry π₁)) (comp (unit _) (curry π₁)))    ≈⟨ comp-cong eq-refl (pair-cong (id-l _) (unit-unique _)) ⟩
    comp apply (pair (curry π₁) (unit _))                                    ≈⟨ comp-cong eq-refl (pair-to-lift _ _) ⟩
    comp apply (comp (pair (comp (curry π₁) π₁) π₂) (pair (id a) (unit _)))  ≈⟨ eq-sym (assoc _ _ _) ⟩
    comp (comp apply (pair (comp (curry π₁) π₁) π₂)) (pair (id a) (unit _))  ≈⟨ comp-cong (β-apply _) eq-refl ⟩
    comp π₁ (pair (id a) (unit _))                                           ≈⟨ β-π₁ ⟩
    id a  ∎ where open EqR (Homs _ _)

  -- from ∘ to = id

  from-to : ∀{a} → Eq (comp from to) (id (Arr Unit a))
  from-to {a} = begin
    comp from to                                                   ≈⟨ eq-refl ⟩
    comp (curry π₁) (comp apply (pair (id _) (unit _)))            ≈⟨ curry-nat _ _ ⟩
    curry (comp π₁ (lift (comp apply (pair (id _) (unit _)))))     ≈⟨ curry-cong β-π₁ ⟩
    curry (comp (comp apply (pair (id _) (unit _))) π₁)            ≈⟨ curry-cong (assoc _ _ _) ⟩
    curry (comp apply (comp (pair (id _) (unit _)) π₁))            ≈⟨ curry-cong (comp-cong eq-refl (pair-nat _ _ _)) ⟩
    curry (comp apply (pair (comp (id _) π₁) (comp (unit _) π₁)))  ≈⟨ curry-cong (comp-cong eq-refl (pair-cong (id-l _) (unit-unique _))) ⟩
    curry (comp apply (pair π₁ (unit _)))                          ≈⟨ curry-cong (comp-cong eq-refl (pair-cong eq-refl (eq-sym (unit-unique _)))) ⟩
    curry (comp apply (pair π₁ π₂))                                ≈⟨ curry-cong (comp-cong eq-refl pair-π) ⟩
    curry (comp apply (id _))                                      ≈⟨ curry-cong (id-r _) ⟩
    curry apply                                                    ≈⟨ curry-apply ⟩
    id (Arr Unit a)
    ∎ where open EqR (Homs _ _)
