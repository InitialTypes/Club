module free-monoids.normal-form
  (X : Set)
  where

open import Level
  using    ()
  renaming (zero to ℓ0) -- \ell

open import Relation.Binary
  using (Preorder; Setoid)
open Preorder
  using    (Carrier)
  renaming (refl to ≤-refl; trans to ≤-trans) -- \leq4
open Setoid
  using    (Carrier)
  renaming (refl to ≋-refl; sym to ≋-sym; trans to ≋-trans) -- \~~~

open import Relation.Binary.Construct.Closure.Equivalence.Properties
  using    ()
  renaming (a—↠b⇒a↔b to ⟶⋆⇒∼; a—↠b⇒b↔a to ⟶⋆⇒∼˘)

open import Relation.Binary.PropositionalEquality
  using    (_≡_)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂; subst to ≡-subst; isEquivalence to ≡-equiv)
import Relation.Binary.PropositionalEquality.Properties as Equality

open import free-monoids.theory X

infix 3 _⊢Ne_ _⊢Ne'_ _⊢Nf_

-- Normal forms (either a (nonempty) right-associated list (cons
-- list) of generators or the unit; we just as well could have
-- picked left association (snoc lists) or lists that end/begin with
-- the unit)
data Ne  : (Γ : Ctx) → (a : Ty) → Set
data Ne' : (Γ : Ctx) → (a : Ty) → Set
data Nf  : (Γ : Ctx) → (a : Ty) → Set

_⊢Ne_  = Ne
_⊢Ne'_ = Ne'
_⊢Nf_  = Nf

data Ne where
  -- var :
  --       (n : Γ ⊢Var a) →
  --       ----------------
  --       Γ ⊢Ne a

  ⌜_⌝ :
        (x : X) →
        ----------------
        Γ ⊢Ne ∗

data Ne' where
  ne  :
        (n : Γ ⊢Ne a) →
        ----------------
        Γ ⊢Ne' a

  _•_ :
        (n : Γ ⊢Ne  ∗) →
        (m : Γ ⊢Ne' ∗) →
        ----------------
        Γ ⊢Ne' ∗

data Nf where
  ne' :
        (n : Γ ⊢Ne' a) →
        ----------------
        Γ ⊢Nf a

  e   :

        ----------------
        Γ ⊢Nf ∗

Nf-preorder : (Γ : Ctx) → (a : Ty) → Preorder ℓ0 ℓ0 ℓ0
Nf-preorder = λ Γ a → Equality.preorder (Nf Γ a)

Nf-setoid : (Γ : Ctx) → (a : Ty) → Setoid ℓ0 ℓ0
Nf-setoid Γ a = Equality.setoid (Nf Γ a)

embNe : (n : Ne Γ a) → Tm Γ a
-- embNe (var n) = var n
embNe ⌜ x ⌝   = ⌜ x ⌝

embNe' : (n : Ne' Γ a) → Tm Γ a
embNe' (ne n)  = embNe n
embNe' (n • m) = embNe n • embNe' m

embNf : (n : Nf Γ a) → Tm Γ a
embNf (ne' n) = embNe' n
embNf e       = e

_++'_ : (n m : Ne' Γ ∗) → Ne' Γ ∗
ne n     ++' m = n • m
(n • m') ++' m = n • (m' ++' m)

_++_ : (n m : Nf Γ ∗) → Nf Γ ∗
ne' n ++ ne' m = ne' (n ++' m)
ne' n ++ e     = ne' n
e     ++ m     = m

nil : Nf Γ ∗
nil = e

++-identityˡ : (n : Nf Γ ∗) → nil ++ n ≡ n -- \^l4
++-identityˡ n = ≡-refl

++-identityʳ : (n : Nf Γ ∗) → n ++ nil ≡ n -- \^r4
++-identityʳ (ne' n) = ≡-refl
++-identityʳ e       = ≡-refl

++'-assoc : (n m o : Ne' Γ ∗) → (n ++' m) ++' o ≡ n ++' (m ++' o)
++'-assoc (ne n)   m o = ≡-refl
++'-assoc (n • n') m o = ≡-cong (n •_) (++'-assoc n' m o)

++-assoc : (n m o : Nf Γ ∗) → (n ++ m) ++ o ≡ n ++ (m ++ o)
++-assoc (ne' n) (ne' m) (ne' o) = ≡-cong ne' (++'-assoc n m o)
++-assoc (ne' n) (ne' m) e       = ≡-refl
++-assoc (ne' n) e       o       = ≡-refl
++-assoc e       m       o       = ≡-refl

[_] : (x : X) → Nf Γ ∗
[ x ] = ne' (ne ⌜ x ⌝)

embNf-pres-≋ : ∀ {n n' : Nf Γ ∗} (n≋n' : n ≋[ Nf-setoid Γ ∗ ] n') → embNf n ≋[ Tm-setoid Γ ∗ ] embNf n'
embNf-pres-≋ {Γ = Γ} n≡n' = ≋-reflexive[ Tm-setoid Γ ∗ ] (≡-cong embNf n≡n')

embNe'-pres-• : ∀ (n m : Ne' Γ ∗) → embNe' n • embNe' m ⟶⋆ embNe' (n ++' m)
embNe'-pres-• (ne n)   m = ⟶⋆-refl
embNe'-pres-• (n • n') m = ⟶⋆-trans (assoc-right⋆ (embNe n) (embNe' n') (embNe' m)) (⟶⋆-cong-•-right (embNe n) (embNe'-pres-• n' m))

embNf-pres-• : ∀ (n m : Nf Γ ∗) → embNf n • embNf m ⟶⋆ embNf (n ++ m)
embNf-pres-• (ne' n) (ne' m) = embNe'-pres-• n m
embNf-pres-• (ne' n) e       = unit-right⋆ (embNe' n)
embNf-pres-• e       m       = unit-left⋆ (embNf m)

embNf-pres-e : embNf nil ≤[ Tm-preorder Γ ∗ ] e
embNf-pres-e {Γ = Γ} = ≤-refl[ Tm-preorder Γ ∗ ] e

embNf-pres-⌜⌝ : ∀ (x : X) → embNf [ x ] ≤[ Tm-preorder Γ ∗ ] ⌜ x ⌝
embNf-pres-⌜⌝ {Γ = Γ} x = ≤-refl[ Tm-preorder Γ ∗ ] ⌜ x ⌝

embNf-pres-•-∼ : ∀ (n m : Nf Γ ∗) → embNf (n ++ m) ≋[ Tm-setoid Γ ∗ ] embNf n • embNf m
embNf-pres-•-∼ n m = ⟶⋆⇒∼˘ (embNf-pres-• n m)

embNf-pres-e-∼ : embNf nil ≋[ Tm-setoid Γ ∗ ] e
embNf-pres-e-∼ {Γ = Γ} = ≋-refl[ Tm-setoid Γ ∗ ] e

embNf-pres-⌜⌝-∼ : ∀ (x : X) → embNf [ x ] ≋[ Tm-setoid Γ ∗ ] ⌜ x ⌝
embNf-pres-⌜⌝-∼ {Γ = Γ} x = ≋-refl[ Tm-setoid Γ ∗ ] ⌜ x ⌝
