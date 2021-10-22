module free-monoids.theory.reduction.coherence
  (X : Set)
  where

open import Relation.Binary
  using (Setoid)

open Setoid
  using    (Carrier)
  renaming (refl to ≋-refl; sym to ≋-sym; trans to ≋-trans)

import Relation.Binary.Construct.Closure.Equivalence as EqClosure

import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties as StarProperties

open import Relation.Binary.PropositionalEquality
  using    (_≡_)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂; subst to ≡-subst; isEquivalence to ≡-equiv)

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import free-monoids.theory.signature X
open import free-monoids.theory.reduction X

infix 19 _≈'_ _≈_

private
  variable
    o o' o'' : t ⟶⋆ t'
    p p' p'' : t ⟶⋆ t'
    q q' q'' : t ⟶⋆ t'

⟶⋆-cong-•-left-pres-id : ∀ (u : Tm Γ ∗) → ⟶⋆-cong-•-left u (id⋆ t) ≡ id⋆ (t • u)
⟶⋆-cong-•-left-pres-id _u = ≡-refl

⟶⋆-cong-•-left-pres-∙ : ∀ (u : Tm Γ ∗) (o : t ⟶⋆ t') (p : t' ⟶⋆ t'') → ⟶⋆-cong-•-left u (o ∙⋆ p) ≡ ⟶⋆-cong-•-left u o ∙⋆ ⟶⋆-cong-•-left u p
⟶⋆-cong-•-left-pres-∙ u o p = StarProperties.gmap-◅◅ _ (cong-left u) o p

⟶⋆-cong-•-right-pres-id : ⟶⋆-cong-•-right t (id⋆ u) ≡ id⋆ (t • u)
⟶⋆-cong-•-right-pres-id = ≡-refl

⟶⋆-cong-•-right-pres-∙ : ∀ (o : u ⟶⋆ u') (p : u' ⟶⋆ u'') (t : Tm Γ ∗) → ⟶⋆-cong-•-right t (o ∙⋆ p) ≡ ⟶⋆-cong-•-right t o ∙⋆ ⟶⋆-cong-•-right t p
⟶⋆-cong-•-right-pres-∙ o p t = StarProperties.gmap-◅◅ _ (cong-right t) o p

⟶⋆-cong-•-pres-id : ⟶⋆-cong-• (id⋆ t) (id⋆ u) ≡ id⋆ (t • u)
⟶⋆-cong-•-pres-id = ≡-refl

data _≈'_ : {t t' : Tm Γ a} → (o p : t ⟶⋆ t') → Set where -- \~~, XXX: for lack of another symbol
  ≈'-cong-∙⋆-left : ∀ (o≈o' : o ≈' o') (p : t' ⟶⋆ t'') → o ∙⋆ p ≈' o' ∙⋆ p

  ≈'-cong-∙⋆-right : ∀ (o : t ⟶⋆ t') (p≈p' : p ≈' p') → o ∙⋆ p ≈' o ∙⋆ p'

  ≈'-⟶⋆-cong-•-functoriality : ∀ (o : u ⟶⋆ u') (p : t ⟶⋆ t') → ⟶⋆-cong-•-left t o ∙⋆ ⟶⋆-cong-•-right u' p ≈' ⟶⋆-cong-•-right u p ∙⋆ ⟶⋆-cong-•-left t' o

  assoc-right-naturality : ⟶⋆-cong-• (⟶⋆-cong-• o p) q ∙⋆ assoc-right⋆ t' u' v' ≈' assoc-right⋆ t u v ∙⋆ ⟶⋆-cong-• o (⟶⋆-cong-• p q)

  unit-left-naturality : ⟶⋆-cong-•-right e o ∙⋆ unit-left⋆ t' ≈' unit-left⋆ t ∙⋆ o

  unit-right-naturality : ⟶⋆-cong-•-left e o ∙⋆ unit-right⋆ t' ≈' unit-right⋆ t ∙⋆ o

  triangle : ⟶⋆-cong-•-left u (unit-right⋆ t) ≈' assoc-right⋆ t _ u ∙⋆ ⟶⋆-cong-•-right t (unit-left⋆ u)

  pentagon : ⟶⋆-cong-•-left w (assoc-right⋆ t u v) ∙⋆ assoc-right⋆ t (u • v) w ∙⋆ ⟶⋆-cong-•-right t (assoc-right⋆ u v w) ≈' assoc-right⋆ (t • u) v w ∙⋆ assoc-right⋆ t u (v • w)

_≈_ : {t t' : Tm Γ a} → (o p : t ⟶⋆ t') → Set
_≈_ = EqClosure.EqClosure _≈'_

⟶⋆-setoid : (t t' : Tm Γ a) → Setoid _ _
⟶⋆-setoid t t' = EqClosure.setoid (_≈'_ {t = t} {t'})

module _ {t t' : Tm Γ a} where
  open Setoid (⟶⋆-setoid t t') using () renaming (refl to ≈-refl; reflexive to ≈-reflexive; sym to ≈-sym; trans to ≈-trans) public

≈-cong-∙⋆-left : ∀ (o≈o' : o ≈ o') (p : t' ⟶⋆ t'') → o ∙⋆ p ≈ o' ∙⋆ p
≈-cong-∙⋆-left o≈o' p = EqClosure.gmap (_∙⋆ p) (λ q≈'q' → ≈'-cong-∙⋆-left q≈'q' p) o≈o'

≈-cong-∙⋆-right : ∀ (o : t ⟶⋆ t') (p≈p' : p ≈ p') → o ∙⋆ p ≈ o ∙⋆ p'
≈-cong-∙⋆-right o = EqClosure.gmap (o ∙⋆_) (≈'-cong-∙⋆-right o)

≈-cong-∙⋆ : (o≈o' : o ≈ o') → (p≈p' : p ≈ p') → o ∙⋆ p ≈ o' ∙⋆ p'
≈-cong-∙⋆ {_Γ} {_a} {_t} {_t'} {_o} {o'} {_t''} {p} {_p'} o≈o' p≈p' = ≈-trans (≈-cong-∙⋆-left o≈o' p) (≈-cong-∙⋆-right o' p≈p')

≈-⟶⋆-cong-•-functoriality : ∀ (o : u ⟶⋆ u') (p : t ⟶⋆ t') → ⟶⋆-cong-•-left t o ∙⋆ ⟶⋆-cong-•-right u' p ≈ ⟶⋆-cong-•-right u p ∙⋆ ⟶⋆-cong-•-left t' o
≈-⟶⋆-cong-•-functoriality o p = EqClosure.return (≈'-⟶⋆-cong-•-functoriality o p)

⟶⋆-cong-•-pres-∙ : ⟶⋆-cong-• (o ∙⋆ o') (p ∙⋆ p') ≈ ⟶⋆-cong-• o p ∙⋆ ⟶⋆-cong-• o' p'
⟶⋆-cong-•-pres-∙ {_Γ} {_t} {t'} {o} {t''} {o'} {u} {u'} {p} {_u''} {p'} = let open SetoidReasoning (⟶⋆-setoid _ _) in begin
    ⟶⋆-cong-• (o ∙⋆ o') (p ∙⋆ p')
  ≡⟨⟩
    ⟶⋆-cong-•-left u (o ∙⋆ o') ∙⋆ ⟶⋆-cong-•-right t'' (p ∙⋆ p')
  ≡⟨ ≡-cong₂ _∙⋆_ (⟶⋆-cong-•-left-pres-∙ u o o') (⟶⋆-cong-•-right-pres-∙ p p' t'') ⟩
    (⟶⋆-cong-•-left u o ∙⋆ ⟶⋆-cong-•-left u o') ∙⋆ ⟶⋆-cong-•-right t'' p ∙⋆ ⟶⋆-cong-•-right t'' p'
  ≡⟨ ∙⋆-assoc (⟶⋆-cong-•-left u o) (⟶⋆-cong-•-left u o') _ ⟩
    ⟶⋆-cong-•-left u o ∙⋆ ⟶⋆-cong-•-left u o' ∙⋆ ⟶⋆-cong-•-right t'' p ∙⋆ ⟶⋆-cong-•-right t'' p'
  ≡˘⟨ ≡-cong (⟶⋆-cong-•-left u o ∙⋆_) (∙⋆-assoc (⟶⋆-cong-•-left u o') (⟶⋆-cong-•-right t'' p) _) ⟩
    ⟶⋆-cong-•-left u o ∙⋆ (⟶⋆-cong-•-left u o' ∙⋆ ⟶⋆-cong-•-right t'' p) ∙⋆ ⟶⋆-cong-•-right t'' p'
  ≈⟨ ≈-cong-∙⋆-right (⟶⋆-cong-•-left u o) (≈-cong-∙⋆-left (≈-⟶⋆-cong-•-functoriality o' p) (⟶⋆-cong-•-right t'' p')) ⟩
    ⟶⋆-cong-•-left u o ∙⋆ (⟶⋆-cong-•-right t' p ∙⋆ ⟶⋆-cong-•-left u' o') ∙⋆ ⟶⋆-cong-•-right t'' p'
  ≡⟨ ≡-cong (⟶⋆-cong-•-left u o ∙⋆_) (∙⋆-assoc (⟶⋆-cong-•-right t' p) (⟶⋆-cong-•-left u' o') _) ⟩
    ⟶⋆-cong-•-left u o ∙⋆ ⟶⋆-cong-•-right t' p ∙⋆ ⟶⋆-cong-•-left u' o' ∙⋆ ⟶⋆-cong-•-right t'' p'
  ≡⟨⟩
    ⟶⋆-cong-•-left u o ∙⋆ ⟶⋆-cong-•-right t' p ∙⋆ ⟶⋆-cong-• o' p'
  ≡˘⟨ ∙⋆-assoc (⟶⋆-cong-•-left u o) (⟶⋆-cong-•-right t' p) _ ⟩
    (⟶⋆-cong-•-left u o ∙⋆ ⟶⋆-cong-•-right t' p) ∙⋆ ⟶⋆-cong-• o' p'
  ≡⟨⟩
    ⟶⋆-cong-• o p ∙⋆ ⟶⋆-cong-• o' p'
  ∎
