module free-monoids.theory
  (X : Set)
  where

open import Level
  using    ()
  renaming (zero to ℓ0) -- \ell

open import Relation.Binary
  using (Preorder; Setoid)

open Preorder
  using    (Carrier)
  renaming (refl to ≤-refl; trans to ≤-trans) -- \leq
open Setoid
  using    (Carrier)
  renaming (refl to ≋-refl; sym to ≋-sym; trans to ≋-trans)

open import Relation.Binary.PropositionalEquality
  using    (_≡_)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂; subst to ≡-subst; isEquivalence to ≡-equiv)

infix 4 ≤-syntax ≋-syntax

≤-syntax : (A : Preorder ℓ0 ℓ0 ℓ0) → (x y : A .Carrier) → Set -- \leq4
≤-syntax A = A .Preorder._∼_
syntax ≤-syntax A x y = x ≤[ A ] y

≤-refl[_] : (A : Preorder ℓ0 ℓ0 ℓ0) → ∀ (x : A .Carrier) → x ≤[ A ] x
≤-refl[ A ] _x = Preorder.refl A

≤-reflexive[_] : (A : Preorder ℓ0 ℓ0 ℓ0) → ∀ {x y : A .Carrier} (x≈y : A .Preorder._≈_ x y) → x ≤[ A ] y
≤-reflexive[ A ] = Preorder.reflexive A

≤-reflexive˘[_] : (A : Preorder ℓ0 ℓ0 ℓ0) → ∀ {x y : A .Carrier} (y≈x : A .Preorder._≈_ y x) → x ≤[ A ] y
≤-reflexive˘[ A ] y≈x = Preorder.reflexive A (Preorder.Eq.sym A y≈x)

≤-trans[_] : (A : Preorder ℓ0 ℓ0 ℓ0) → ∀ {x y z : A .Carrier} (x≤y : x ≤[ A ] y) (y≤z : y ≤[ A ] z) → x ≤[ A ] z
≤-trans[ A ] = Preorder.trans A

≋-syntax : (A : Setoid ℓ0 ℓ0) → (x y : A .Carrier) → Set -- \~~~
≋-syntax A = A .Setoid._≈_
syntax ≋-syntax A x y = x ≋[ A ] y

≋-refl[_] : (A : Setoid ℓ0 ℓ0) → ∀ (x : A .Carrier) → x ≋[ A ] x
≋-refl[ A ] _x = A .Setoid.refl

≋-reflexive[_] : (A : Setoid ℓ0 ℓ0) → ∀ {x y : A .Carrier} (x≡y : x ≡ y) → x ≋[ A ] y
≋-reflexive[ A ] = Setoid.reflexive A

≋-sym[_] : (A : Setoid ℓ0 ℓ0) → ∀ {x y : A .Carrier} → x ≋[ A ] y → y ≋[ A ] x
≋-sym[ A ] = A .Setoid.sym

≋-trans[_] : (A : Setoid ℓ0 ℓ0) → ∀ {x y z : A .Carrier} (x≋y : x ≋[ A ] y) (y≋z : y ≋[ A ] z) → x ≋[ A ] z
≋-trans[ A ] = A .Setoid.trans

≋-trans˘[_] : (A : Setoid ℓ0 ℓ0) → ∀ {x y z : A .Carrier} (y≋x : y ≋[ A ] x) (y≋z : y ≋[ A ] z) → x ≋[ A ] z
≋-trans˘[ A ] y≋x y≋z = ≋-trans[ A ] (≋-sym[ A ] y≋x) y≋z

open import free-monoids.theory.signature           X public
open import free-monoids.theory.reduction           X public
open import free-monoids.theory.reduction.coherence X public
open import free-monoids.theory.conversion          X public
