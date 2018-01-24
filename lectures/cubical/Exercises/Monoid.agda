{-# OPTIONS --cubical #-}
module Monoid where

open import Cubical.PathPrelude
open import Cubical.Comp


record Monoid : Set₁ where
  field
    M : Set
    unit : M
    _<>_ : M → M → M
    left-unit : ∀ m → unit <> m ≡ m
    right-unit : ∀ m → m <> unit ≡ m
    assoc : ∀ {x y z} → x <> (y <> z) ≡ (x <> y) <> z

open Monoid

-- An equality between elements of Monoid generates a monoid isomorphism.
module _ (A B : Monoid) (eq : A ≡ B) where
  module A = Monoid A
  module B = Monoid B

  -- We can project heterogeneous equalities about the fields.

  unit-lemma : PathP (\ i → eq i .M) A.unit B.unit
  unit-lemma = \ j → eq j .unit

  <>-lemma : PathP (\ i → eq i .M → eq i .M → eq i .M) A._<>_ B._<>_
  <>-lemma = \ j → eq j ._<>_


  -- Use transp, transp-iso, fromPathP to prove the following.
  f : A.M → B.M
  f = {!!}

  f⁻¹ : B.M → A.M
  f⁻¹ = {!!}

  f⁻¹-f : ∀ x → f⁻¹ (f x) ≡ x
  f⁻¹-f x = {!!}

  f-f⁻¹ : ∀ x → f (f⁻¹ x) ≡ x
  f-f⁻¹ x = {!!}

  f-preserves-unit : f A.unit ≡ B.unit
  f-preserves-unit = fromPathP {!!}


  f-preserves-<> : (\ (x y : A.M) → f (x A.<> y)) ≡ (\ x y → f x B.<> f y)
  f-preserves-<> =
   begin
    (λ x y → f (x A.<> y))                 ≡⟨ {!!} ⟩
    (\ x y → f (f⁻¹ (f x) A.<> f⁻¹ (f y))) ≡⟨ {!!} ⟩
    (λ x y → f x B.<> f y)                 ∎


-- Bonus (Hard): use univalence to construct an equality of you Monoid
-- elements out of a monoid isomorphism, do you need some extra
-- assumption?
