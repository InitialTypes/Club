module free-monoids.theory.reduction.deterministic
  (X : Set)
  where

open import Relation.Binary.PropositionalEquality
  using    (_≡_)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂; subst to ≡-subst; isEquivalence to ≡-equiv)

open import free-monoids.theory.signature X
open import free-monoids.theory.reduction X renaming (_⟶_ to _⟶'_) hiding (⊢⟶∶-syntax)

infix 19 _⟶_
infix  3 ⊢⟶∶-syntax

private
  variable
    t₁ t₂ t₃ : Tm Γ a

data _⟶_ : {Γ : Ctx} → {a : Ty} → (t t' : Tm Γ a) → Set -- \-->

⊢⟶∶-syntax = λ Γ a t t' → _⟶_ {Γ} {a} t t' -- \vdash \--> \:
syntax ⊢⟶∶-syntax Γ a t t' = Γ ⊢ t ⟶ t' ∶ a

data _⟶_ where
  unit-left :
                 (w : Γ ⊢ ∗) →
                 -----------------------------------------
                 Γ ⊢ e • w ⟶ w ∶ ∗

  unit-left' :   -- alternative to assoc-right'
                 (t w : Γ ⊢ ∗) →
                 -----------------------------------------
                 Γ ⊢ (e • t) • w ⟶ t • w ∶ ∗

  unit-right :
                 (x : X) →
                 -----------------------------------------
                 Γ ⊢ ⌜ x ⌝ • e ⟶ ⌜ x ⌝ ∶ ∗

  assoc-right :
                 (x   : X) →
                 (t w : Γ ⊢ ∗) →
                 -----------------------------------------
                 Γ ⊢ (⌜ x ⌝ • t) • w ⟶ ⌜ x ⌝ • (t • w) ∶ ∗

  -- assoc-right' : -- alternative to unit-left'
  --                (t w : Γ ⊢ ∗) →
  --                -----------------------------------------
  --                Γ ⊢ (e • t) • w ⟶ e • (t • w) ∶ ∗

  cong-left :
                 (w    : Γ ⊢ ∗) →
                 (t⟶t' : Γ ⊢ (t₁ • t₂) • t₃ ⟶ t' ∶ ∗) →
                 -----------------------------------------
                 Γ ⊢ ((t₁ • t₂) • t₃) • w ⟶ t' • w ∶ ∗

  cong-right :
                 (x    : X) →
                 (t⟶t' : Γ ⊢ t ⟶ t' ∶ ∗) →
                 -----------------------------------------
                 Γ ⊢ ⌜ x ⌝ • t ⟶ ⌜ x ⌝ • t' ∶ ∗

⟶-irrelevant : (p p' : t ⟶ t') → p' ≡ p
⟶-irrelevant (unit-left w)       (unit-left .w)         = ≡-refl
⟶-irrelevant (unit-left' t w)    (unit-left' .t .w)     = ≡-refl
⟶-irrelevant (unit-right x)      (unit-right .x)        = ≡-refl
⟶-irrelevant (assoc-right x t w) (assoc-right .x .t .w) = ≡-refl
-- ⟶-irrelevant (assoc-right' t w)  (assoc-right' .t .w)   = ≡-refl
⟶-irrelevant (cong-left w p)     (cong-left .w p')      = ≡-cong (cong-left w)  (⟶-irrelevant p p')
⟶-irrelevant (cong-right x p)    (cong-right .x p')     = ≡-cong (cong-right x) (⟶-irrelevant p p')

⟶-functional : (_p : t ⟶ t') → (_p' : t ⟶ t'') → t'' ≡ t'
⟶-functional (unit-left w)       (unit-left .w)         = ≡-refl
⟶-functional (unit-left' t w)    (unit-left' .t .w)     = ≡-refl
⟶-functional (unit-right x)      (unit-right .x)        = ≡-refl
⟶-functional (assoc-right x t w) (assoc-right .x .t .w) = ≡-refl
-- ⟶-functional (assoc-right' t w)  (assoc-right' .t .w)   = ≡-refl
⟶-functional (cong-left w p)     (cong-left .w p')      = ≡-cong (_• w)     (⟶-functional p p')
⟶-functional (cong-right x p)    (cong-right .x p')     = ≡-cong (⌜ x ⌝ •_) (⟶-functional p p')

embed : (_p : t ⟶ t') → t ⟶' t'
embed (unit-left w)       = unit-left w
embed (unit-left' t w)    = cong-left w (unit-left t)
embed (unit-right x)      = unit-right ⌜ x ⌝
embed (assoc-right x t w) = assoc-right ⌜ x ⌝ t w
-- embed (assoc-right' t w)  = assoc-right e t w
embed (cong-left w t⟶t')  = cong-left w (embed t⟶t')
embed (cong-right x t⟶t') = cong-right ⌜ x ⌝ (embed t⟶t')

-- normalize : (_p : t ⟶' t') → t ⟶ t'
