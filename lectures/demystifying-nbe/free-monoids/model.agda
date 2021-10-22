module free-monoids.model
  (X : Set)
  where

open import Data.Product
  using (_×_; _,_)
open import Data.Unit
  using (⊤; tt)

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
  renaming (refl to ≋-refl; sym to ≋-sym; trans to ≋-trans)

import Relation.Binary.Construct.Always as Total
  renaming (Always to Rel)

import Relation.Binary.Construct.Closure.Equivalence as EqClosure

import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star

open import Relation.Binary.PropositionalEquality
  using    (_≡_)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂; subst to ≡-subst; isEquivalence to ≡-equiv)

open import free-monoids.theory X as theory
  hiding (Tm; Tm-preorder; Tm-setoid)
import free-monoids.normal-form X as normal-form

-- TODO: add to stdlib
module _ {ℓ ℓ′ a : Level.Level} {A : Set a} (_≈_ : Relation.Binary.Rel A ℓ) (≈-equiv : Relation.Binary.IsEquivalence _≈_) where
  isPreorder : Relation.Binary.IsPreorder _≈_ (Total.Rel {a} {ℓ′})
  isPreorder = record { isEquivalence = ≈-equiv ; reflexive = λ _ → _ ; trans = λ {i} {j} {k} x y → Total.trans {a} A ℓ′ {i} {j} {k} x y }

private
  Tm          = theory.Tm               [] ∗
  Tm-preorder = theory.Tm-preorder      [] ∗
  Tm-setoid   = theory.Tm-setoid        [] ∗
  Ne          = normal-form.Ne          [] ∗
  Ne'         = normal-form.Ne'         [] ∗
  Nf          = normal-form.Nf          [] ∗
  Nf-preorder = normal-form.Nf-preorder [] ∗
  Nf-setoid   = normal-form.Nf-setoid   [] ∗

-- Monoid, model
record Mod : Set₁ where
  field
    M : Setoid ℓ0 ℓ0

    _++_      : (xs ys : M .Carrier) → M .Carrier
    ≋-cong-++ : ∀ {xs xs' ys ys' : M .Carrier} (xs≋xs' : xs ≋[ M ] xs') (ys≋ys' : ys ≋[ M ] ys') → xs ++ ys ≋[ M ] xs' ++ ys'

    nil : M .Carrier

    [_] : (x : X) → M .Carrier

    ++-identityˡ : ∀ (xs : M .Carrier) → nil ++ xs ≋[ M ] xs -- \^l4
    ++-identityʳ : ∀ (xs : M .Carrier) → xs ++ nil ≋[ M ] xs -- \^r4
    ++-assoc     : ∀ (xs ys zs : M .Carrier) → (xs ++ ys) ++ zs ≋[ M ] xs ++ (ys ++ zs)

-- "Directed" model
record Mod' : Set₁ where
  field
    M : Preorder ℓ0 ℓ0 ℓ0

    _++_      : (xs ys : M .Carrier) → M .Carrier
    ≤-cong-++ : ∀ {xs xs' ys ys' : M .Carrier} (xs≋xs' : xs ≤[ M ] xs') (ys≋ys' : ys ≤[ M ] ys') → xs ++ ys ≤[ M ] xs' ++ ys'

    nil : M .Carrier

    [_] : (x : X) → M .Carrier

    ++-identityˡ : ∀ (xs : M .Carrier) → nil ++ xs ≤[ M ] xs -- \^l4
    ++-identityʳ : ∀ (xs : M .Carrier) → xs ++ nil ≤[ M ] xs -- \^r4
    ++-assoc     : ∀ (xs ys zs : M .Carrier) → (xs ++ ys) ++ zs ≤[ M ] xs ++ (ys ++ zs)

-- Free monoid, initial model, free model, term model
𝒯𝓂 : Mod -- \McT \Mcm
𝒯𝓂 = record
  { M            = Tm-setoid
  ; _++_         = _•_
  ; ≋-cong-++    = ∼-cong-•
  ; nil          = e
  ; [_]          = ⌜_⌝
  ; ++-identityˡ = unit-left∼
  ; ++-identityʳ = unit-right∼
  ; ++-assoc     = assoc-right∼
  }

-- "Directed" term model
𝒯𝓂' : Mod' -- \McT \Mcm
𝒯𝓂' = record
  { M            = Tm-preorder
  ; _++_         = _•_
  ; ≤-cong-++    = ⟶⋆-cong-•
  ; nil          = e
  ; [_]          = ⌜_⌝
  ; ++-identityˡ = unit-left⋆
  ; ++-identityʳ = unit-right⋆
  ; ++-assoc     = assoc-right⋆
  }

𝒩𝒻 : Mod -- \McN \Mcf
𝒩𝒻 = record
  { M            = Nf-setoid
  ; _++_         = normal-form._++_
  ; ≋-cong-++    = ≡-cong₂ normal-form._++_
  ; nil          = normal-form.nil
  ; [_]          = normal-form.[_]
  ; ++-identityˡ = normal-form.++-identityˡ
  ; ++-identityʳ = normal-form.++-identityʳ
  ; ++-assoc     = normal-form.++-assoc
  }

𝒩𝒻' : Mod' -- \McN \Mcf
𝒩𝒻' = record
  { M            = Nf-preorder
  ; _++_         = normal-form._++_
  ; ≤-cong-++    = ≡-cong₂ normal-form._++_
  ; nil          = normal-form.nil
  ; [_]          = normal-form.[_]
  ; ++-identityˡ = normal-form.++-identityˡ
  ; ++-identityʳ = normal-form.++-identityʳ
  ; ++-assoc     = normal-form.++-assoc
  }

-- Dependent monoid, logical predicate
record Pred (ℳ : Mod) : Set₁ where
  open Mod ℳ

  field
    P : (xs : M .Carrier) → Setoid ℓ0 ℓ0

    pres-≋ : ∀ {xs xs' : M .Carrier} (xs≋xs' : xs ≋[ M ] xs') (p : P xs .Carrier) → P xs' .Carrier

    pres-++        : ∀ {xs ys : M .Carrier} (p : P xs .Carrier) (q : P ys .Carrier) → P (xs ++ ys) .Carrier
    ≋-cong-pres-++ : ∀ {xs ys : M .Carrier} {p p' : P xs .Carrier} {q q' : P ys .Carrier} (p≋p' : p ≋[ P xs ] p') (q≋q' : q ≋[ P ys ] q') → pres-++ p q ≋[ P (xs ++ ys) ] pres-++ p' q'

    pres-nil : P nil .Carrier

    pres-[] : ∀ (x : X) → P [ x ] .Carrier

    pres-++-identityˡ : ∀ {xs : M .Carrier} (p : P xs .Carrier) → pres-≋ (++-identityˡ xs) (pres-++ pres-nil p) ≋[ P xs ] p
    pres-++-identityʳ : ∀ {xs : M .Carrier} (p : P xs .Carrier) → pres-≋ (++-identityʳ xs) (pres-++ p pres-nil) ≋[ P xs ] p
    pres-++-assoc     : ∀ {xs ys zs : M .Carrier} (p : P xs .Carrier) (q : P ys .Carrier) (r : P zs .Carrier) → pres-≋ (++-assoc xs ys zs) (pres-++ (pres-++ p q) r) ≋[ P (xs ++ (ys ++ zs)) ] pres-++ p (pres-++ q r)

-- "Directed" dependent model over a "directed" model
record Pred' (ℳ : Mod') : Set₁ where
  open Mod' ℳ

  field
    P : (xs : M .Carrier) → Preorder ℓ0 ℓ0 ℓ0

    -- pres-≤ : ∀ {xs xs' : M .Carrier} (xs≤xs' : xs ≤[ M ] xs') (p : P xs .Carrier) → P xs' .Carrier
    pres-≤˘ : ∀ {xs xs' : M .Carrier} (xs≤xs' : xs ≤[ M ] xs') (p : P xs' .Carrier) → P xs .Carrier

    pres-++        : ∀ {xs ys : M .Carrier} (p : P xs .Carrier) (q : P ys .Carrier) → P (xs ++ ys) .Carrier
    ≤-cong-pres-++ : ∀ {xs ys : M .Carrier} {p p' : P xs .Carrier} {q q' : P ys .Carrier} (p≤p' : p ≤[ P xs ] p') (q≤q' : q ≤[ P ys ] q') → pres-++ p q ≤[ P (xs ++ ys) ] pres-++ p' q'

    pres-nil : P nil .Carrier

    pres-[] : ∀ (x : X) → P [ x ] .Carrier

    pres-++-identityˡ : ∀ {xs : M .Carrier} (p : P xs .Carrier) → pres-++ pres-nil p ≤[ P (nil ++ xs) ] pres-≤˘ (++-identityˡ xs) p
    pres-++-identityʳ : ∀ {xs : M .Carrier} (p : P xs .Carrier) → pres-++ p pres-nil ≤[ P (xs ++ nil) ] pres-≤˘ (++-identityʳ xs) p
    pres-++-assoc     : ∀ {xs ys zs : M .Carrier} (p : P xs .Carrier) (q : P ys .Carrier) (r : P zs .Carrier) → pres-++ (pres-++ p q) r ≤[ P ((xs ++ ys) ++ zs) ] pres-≤˘ (++-assoc xs ys zs) (pres-++ p (pres-++ q r))

module _
  (ℳ : Mod)
  where

  open Mod ℳ

  constant-predicate : (𝒩 : Mod) → Pred 𝒩 -- \McN
  constant-predicate _𝒩 = record
    { P                 = λ _xs → M
    ; pres-≋            = λ _xs≋xs' m → m
    ; pres-++           = _++_
    ; ≋-cong-pres-++    = ≋-cong-++
    ; pres-nil          = nil
    ; pres-[]           = [_]
    ; pres-++-identityˡ = ++-identityˡ
    ; pres-++-identityʳ = ++-identityʳ
    ; pres-++-assoc     = ++-assoc
    }

module _
  (ℳ : Mod')
  where

  open Mod' ℳ

  constant-predicate' : (𝒩 : Mod') → Pred' 𝒩 -- \McN
  constant-predicate' _𝒩 = record
    { P                 = λ _xs → M
    ; pres-≤˘           = λ _xs≤xs' m → m
    ; pres-++           = _++_
    ; ≤-cong-pres-++    = ≤-cong-++
    ; pres-nil          = nil
    ; pres-[]           = [_]
    ; pres-++-identityˡ = ++-identityˡ
    ; pres-++-identityʳ = ++-identityʳ
    ; pres-++-assoc     = ++-assoc
    }

-- TODO: add `proof-irrelevant-predicate` (cf. uniqueness part of initiality below and adequacy of normalization in `normalization.agda`)

-- TODO: prove that predicates are closed under substitution along homomorphisms

-- Induction
module _
  (𝒫 : Pred 𝒯𝓂)
  where

  open Pred 𝒫

  fundamental-theorem : ∀ (t : Tm) → P t .Carrier
  fundamental-theorem ⌜ x ⌝   = pres-[] x
  fundamental-theorem (t • u) = pres-++ (fundamental-theorem t) (fundamental-theorem u)
  fundamental-theorem e       = pres-nil

-- "Directed" fundamental theorem
module _
  (𝒫 : Pred' 𝒯𝓂')
  where

  open Pred' 𝒫

  fundamental-theorem' : ∀ (t : Tm) → P t .Carrier
  fundamental-theorem' ⌜ x ⌝   = pres-[] x
  fundamental-theorem' (t • u) = pres-++ (fundamental-theorem' t) (fundamental-theorem' u)
  fundamental-theorem' e       = pres-nil

-- Existence part of initiality, interpretation, recursion
module Eval
  (ℳ : Mod) -- \McM
  where

  open Mod ℳ

  -- interpretation of types
  ⟦_⟧Ty-setoid : (a : Ty) → (Γ : Ctx) → Setoid ℓ0 ℓ0 -- \[[ \]]
  ⟦ ∗ ⟧Ty-setoid _Γ = M

  ⟦_⟧Ty : (a : Ty) → (Γ : Ctx) → Set
  ⟦ a ⟧Ty Γ = ⟦ a ⟧Ty-setoid Γ .Carrier

  -- interpretation of contexts
  ⟦_⟧Ctx : (Δ : Ctx) → (Γ : Ctx) → Set
  ⟦ []    ⟧Ctx _Γ = ⊤
  -- ⟦ Δ , a ⟧Ctx Γ  = ⟦ Δ ⟧Ctx Γ × ⟦ a ⟧Ty Γ

  -- -- interpretation of variables
  -- ⟦_⟧Var : (n : Var Δ a) → (δ : ⟦ Δ ⟧Ctx Γ) → ⟦ a ⟧Ty Γ
  -- ⟦ zero   ⟧Var (_δ , xs) = xs
  -- ⟦ succ n ⟧Var (δ , _xs) = ⟦ n ⟧Var δ

  -- interpretation of terms
  ⟦_⟧Tm : (t : Tm) → ⟦ ∗ ⟧Ty []
  ⟦_⟧Tm = fundamental-theorem (constant-predicate ℳ 𝒯𝓂)

  -- interpretation of substitutions
  ⟦_⟧Sub : (s : Sub Θ Δ) → (θ : ⟦ Θ ⟧Ctx Γ) → ⟦ Δ ⟧Ctx Γ
  ⟦ tt    ⟧Sub _θ = tt
  -- ⟦ s , t ⟧Sub θ  = ⟦ s ⟧Sub θ , ⟦ t ⟧Tm θ

  -- TODO: prove for predicates and instantiate with the constant predicate
  soundness : ∀ {t t' : Tm} → (t⟶t' : t ⟶ t') → ⟦ t ⟧Tm ≋[ ⟦ ∗ ⟧Ty-setoid [] ] ⟦ t' ⟧Tm
  soundness (unit-left t)       = ++-identityˡ ⟦ t ⟧Tm
  soundness (unit-right t)      = ++-identityʳ ⟦ t ⟧Tm
  soundness (assoc-right t u v) = ++-assoc ⟦ t ⟧Tm ⟦ u ⟧Tm ⟦ v ⟧Tm
  soundness (cong-left  u t⟶t') = ≋-cong-++ (soundness t⟶t') (≋-refl[ M ] ⟦ u ⟧Tm)
  soundness (cong-right t u⟶u') = ≋-cong-++ (≋-refl[ M ] ⟦ t ⟧Tm) (soundness u⟶u')

  -- interpretation of terms is well-defined, interpretation of terms preserves conversion
  ⟦⟧Tm-pres-≋ : ∀ {t t' : Tm} → (t≋t' : t ≋[ Tm-setoid ] t') → ⟦ t ⟧Tm ≋[ ⟦ ∗ ⟧Ty-setoid [] ] ⟦ t' ⟧Tm
  ⟦⟧Tm-pres-≋ = EqClosure.gfold (⟦ ∗ ⟧Ty-setoid [] .Setoid.isEquivalence) ⟦_⟧Tm soundness

  -- interpretation of terms is then a homomorphism by construction

-- Evaluation in a "directed" model
module Eval'
  (ℳ : Mod') -- \McM
  where

  open Mod' ℳ

  -- interpretation of types
  ⟦_⟧Ty-setoid : (a : Ty) → (Γ : Ctx) → Setoid ℓ0 ℓ0 -- \[[ \]]
  ⟦ ∗ ⟧Ty-setoid _Γ = Preorder.Eq.setoid M

  ⟦_⟧Ty-preorder : (a : Ty) → (Γ : Ctx) → Preorder ℓ0 ℓ0 ℓ0 -- \[[ \]]
  ⟦ ∗ ⟧Ty-preorder _Γ = M

  ⟦_⟧Ty : (a : Ty) → (Γ : Ctx) → Set
  ⟦ a ⟧Ty Γ = ⟦ a ⟧Ty-setoid Γ .Carrier

  -- interpretation of contexts
  ⟦_⟧Ctx : (Δ : Ctx) → (Γ : Ctx) → Set
  ⟦ []    ⟧Ctx _Γ = ⊤
  -- ⟦ Δ , a ⟧Ctx Γ  = ⟦ Δ ⟧Ctx Γ × ⟦ a ⟧Ty Γ

  -- -- interpretation of variables
  -- ⟦_⟧Var : (n : Var Δ a) → (δ : ⟦ Δ ⟧Ctx Γ) → ⟦ a ⟧Ty Γ
  -- ⟦ zero   ⟧Var (_δ , xs) = xs
  -- ⟦ succ n ⟧Var (δ , _xs) = ⟦ n ⟧Var δ

  -- interpretation of terms
  ⟦_⟧Tm : (t : Tm) → ⟦ ∗ ⟧Ty []
  ⟦_⟧Tm = fundamental-theorem' (constant-predicate' ℳ 𝒯𝓂')

  -- interpretation of substitutions
  ⟦_⟧Sub : (s : Sub Θ Δ) → (θ : ⟦ Θ ⟧Ctx Γ) → ⟦ Δ ⟧Ctx Γ
  ⟦ tt    ⟧Sub _θ = tt
  -- ⟦ s , t ⟧Sub θ  = ⟦ s ⟧Sub θ , ⟦ t ⟧Tm θ

  -- TODO: prove for predicates and instantiate with the constant predicate
  soundness : ∀ {t t' : Tm} → (t⟶t' : t ⟶ t') → ⟦ t ⟧Tm ≤[ ⟦ ∗ ⟧Ty-preorder [] ] ⟦ t' ⟧Tm
  soundness (unit-left t)       = ++-identityˡ ⟦ t ⟧Tm
  soundness (unit-right t)      = ++-identityʳ ⟦ t ⟧Tm
  soundness (assoc-right t u v) = ++-assoc ⟦ t ⟧Tm ⟦ u ⟧Tm ⟦ v ⟧Tm
  soundness (cong-left  u t⟶t') = ≤-cong-++ (soundness t⟶t') (≤-refl[ M ] ⟦ u ⟧Tm)
  soundness (cong-right t u⟶u') = ≤-cong-++ (≤-refl[ M ] ⟦ t ⟧Tm) (soundness u⟶u')

  -- interpretation of terms is well-defined, interpretation of terms preserves reduction
  ⟦⟧Tm-pres-≤ : ∀ {t t' : Tm} → (t≤t' : t ≤[ Tm-preorder ] t') → ⟦ t ⟧Tm ≤[ ⟦ ∗ ⟧Ty-preorder [] ] ⟦ t' ⟧Tm
  ⟦⟧Tm-pres-≤ {t} {t'} = Star.gfold ⟦_⟧Tm (⟦ ∗ ⟧Ty-preorder [] .Preorder._∼_) (λ t⟶t' → ≤-trans[ ⟦ ∗ ⟧Ty-preorder [] ] (soundness t⟶t')) {k = t'} (≤-refl[ ⟦ ∗ ⟧Ty-preorder [] ] ⟦ t' ⟧Tm)

  -- interpretation of terms is then a homomorphism by construction

-- Uniqueness part of initiality
module _
  (ℳ : Mod)
  (let open Mod ℳ)
  (h         : (t : Tm) → M .Carrier)
  (h-pres-≋  : ∀ {t t' : Tm} (t≋t' : t ≋[ Tm-setoid ] t') → h t ≋[ M ] h t')
  (h-pres-•  : ∀ (t u : Tm) → h (t • u) ≋[ M ] h t ++ h u)
  (h-pres-e  : h e ≋[ M ] nil)
  (h-pres-⌜⌝ : ∀ (x : X) → h ⌜ x ⌝ ≋[ M ] [ x ])
  where
    open Eval ℳ
    private
      𝒫 : Pred 𝒯𝓂
      𝒫 = record
        { P                 = λ t → record { Carrier = h t ≋[ M ] ⟦ t ⟧Tm ; _≈_ = Total.Rel ; isEquivalence = Total.isEquivalence _ _ }
        ; pres-≋            = λ xs≋xs' hxs≋⟦xs⟧Tm → ≋-trans˘[ M ] (h-pres-≋ xs≋xs') (≋-trans[ M ] hxs≋⟦xs⟧Tm (⟦⟧Tm-pres-≋ xs≋xs'))
        ; pres-++           = λ {xs} {ys} hxs≋⟦xs⟧Tm hys≋⟦ys⟧Tm → ≋-trans[ M ] (h-pres-• xs ys) (≋-cong-++ hxs≋⟦xs⟧Tm hys≋⟦ys⟧Tm)
        ; pres-nil          = h-pres-e
        ; pres-[]           = h-pres-⌜⌝
        ; pres-++-identityˡ = λ _ → _
        ; pres-++-identityʳ = λ _ → _
        ; pres-++-assoc     = λ _ _ _ → _
        }

    uniqueness : ∀ (t : Tm) → h t ≋[ M ] ⟦ t ⟧Tm
    uniqueness = fundamental-theorem 𝒫

-- TODO: prove that homomorphisms are closed under composition
