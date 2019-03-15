open import Terms
open import STLC

open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)
open import Data.Product using (proj₁; proj₂; _,_; Σ)

-- Henkin models are weakly complete
module Henkin.Completeness where

lift-lift : ∀{Γ Δ Ω A} (i : Γ ⊆ Δ) (i′ : Δ ⊆ Ω) →
  ∀{B} (v : Var (Γ , A) B) → (↑⊆ i′ ∘ ↑⊆ i) v ≡ ↑⊆ (i′ ∘ i) v
lift-lift i i′ zero = refl
lift-lift i i′ (suc v) = refl

weak-lift : ∀{Γ Δ Ω A} (i : Γ ⊆ Δ) (i′ : Δ ⊆ Ω) →
  ∀{B} (v : Var Γ B) → (↑⊆ {A = A} i′ ∘ (suc ∘ i)) v ≡ (suc ∘ (i′ ∘ i)) v
weak-lift i i′ zero = refl
weak-lift i i′ (suc v) = refl

weak-extensionality : ∀{Γ Δ A} (i i′ : Γ ⊆ Δ) (t : Term Γ A) →
  (∀{B} (v : Var Γ B) → i v ≡ i′ v) → t ↓ i ≡ t ↓ i′
weak-extensionality i i′ (var v) hyp rewrite hyp v = refl
weak-extensionality {Γ} {Δ} {A} i i′ (abs t) hyp
  rewrite weak-extensionality (↑⊆ i) (↑⊆ i′) t (λ v → {!aux!}) = refl
  where aux : ∀ {A} (v : Var (Γ , A) A) → ↑⊆ i v ≡ ↑⊆ i′ v
        aux zero = refl
        aux (suc v) = cong suc (hyp v)
weak-extensionality i i′ (app t u) hyp
  rewrite weak-extensionality i i′ t hyp |
          weak-extensionality i i′ u hyp
  = refl

weak-comp : ∀{Γ Δ Ω A} (t : Term Γ A) (i : Γ ⊆ Δ) (i′ : Δ ⊆ Ω) →
  (t ↓ i) ↓ i′ ≡ t ↓ (i′ ∘ i)
weak-comp {Γ} {Δ} {Ω} {A} (var v) i i′ = refl
weak-comp {Γ} {Δ} {Ω} {A ⇒ B} (abs t) i i′
  rewrite weak-comp t (↑⊆ i) (↑⊆ i′) |
          weak-extensionality (↑⊆ i′ ∘ ↑⊆ i) (↑⊆ (i′ ∘ i)) t (lift-lift i i′)
          = refl
weak-comp {Γ} {Δ} {Ω} {A} (app t u) i i′
  rewrite weak-comp t i i′ |
          weak-comp u i i′
          = refl

weak-eq : ∀{𝓐 : EqAxioms} {Γ Γ′ A} {t u : Term Γ A} (i : Γ ⊆ Γ′) → 𝓐 ⊢ t ≡λ u → 𝓐 ⊢ (t ↓ i) ≡λ (u ↓ i)
weak-eq {Γ′ = Γ′} i (axiom j x) = {!!} -- need to restrict axioms to closed terms!
weak-eq {Γ′ = Γ′} i (β t u) = {!!} -- easier if we only consider injective renamings...
weak-eq {𝓐} {Γ} {Γ′} {A ⇒ B} i (η {.Γ} {.A} {.B} t)
  rewrite weak-comp t (suc {B = A}) (↑⊆ i) |
          sym (weak-comp t i (suc {B = A}))
          = η (t ↓ i)
weak-eq {Γ′ = Γ′} i (λcong-abs eq) = λcong-abs (weak-eq (↑⊆ i) eq)
weak-eq {Γ′ = Γ′} i (λcong-app eq eq₁) = λcong-app (weak-eq i eq) (weak-eq i eq₁)
weak-eq {Γ′ = Γ′} i λrefl = λrefl
weak-eq {Γ′ = Γ′} i (λsym eq) = λsym (weak-eq i eq)
weak-eq {Γ′ = Γ′} i (λtrans eq eq₁) = λtrans (weak-eq i eq) (weak-eq i eq₁)



-- injective renamings
Injective : ∀{Γ Δ} (i : Γ ⊆ Δ) → Set
Injective i = ∀{A} (v v′ : Var _ A) → i v ≡ i v′ → v ≡ v′

_⊑_ : (Γ Δ : Context) → Set
Γ ⊑ Δ = Σ (∀ {A} → Var Γ A → Var Δ A) (λ i → Injective i)

inj-lift : ∀{Γ Δ A} (i : Γ ⊑ Δ) → Injective (↑⊆ {A = A} (proj₁ i))
inj-lift i zero zero x = refl
inj-lift i zero (suc v′) ()
inj-lift i (suc v) zero ()
inj-lift i (suc v) (suc v′) x = cong suc (proj₂ i v v′ {!x!})

inj-ren-inj : ∀{Γ Δ A} (i : Γ ⊑ Δ) (t t′ : Term Γ A) →
  (t ↓ (proj₁ i) ≡ t′ ↓ (proj₁ i)) → t ≡ t′
inj-ren-inj {Γ} {Δ} {A} i (var v) (var v₁) x = cong var (proj₂ i v v₁ {!x!})
inj-ren-inj {Γ} {Δ} {.(_ ⇒ _)} i (abs t) (abs t′) x = cong abs (inj-ren-inj (↑⊆ (proj₁ i) , inj-lift i) t t′ {!x!})
inj-ren-inj {Γ} {Δ} {A} i (app t t₁) (app t′ t′₁) x = {!cong₂ app ? ?!}
inj-ren-inj {Γ} {Δ} {.(_ ⇒ _)} i (var v) (abs t′) ()
inj-ren-inj {Γ} {Δ} {A} i (var v) (app t′ t′₁) ()
inj-ren-inj {Γ} {Δ} {.(_ ⇒ _)} i (abs t) (var v) ()
inj-ren-inj {Γ} {Δ} {.(_ ⇒ _)} i (abs t) (app t′ t′₁) ()
inj-ren-inj {Γ} {Δ} {A} i (app t t₁) (var v) ()
inj-ren-inj {Γ} {Δ} {.(_ ⇒ _)} i (app t t₁) (abs t′) ()



streng-eq : ∀{Γ Γ′ A} {i : Γ′ ⊆ Γ} {t u : Term Γ A} {t′ u′} → -- (i : Γ ⊑ Δ) instead
  t′ ↓ i ≡ t → u′ ↓ i ≡ u → t ≡λ u → t′ ≡λ u′ 
streng-eq {Γ} {Γ′} {A} {i} {.(_ ↓ j)} {.(_ ↓ j)} {t′} {u′} t′t u′u (axiom j ())

streng-eq {Γ} {Γ′} {A} {i} {.(app (abs t) u)} {.(t /x← u)} {app (abs t′) t′₁} {u′} t′t u′u (β t u) = {!β t′ t′₁!}

streng-eq {Γ} {Γ′} {.(_ ⇒ _)} {i} {t} {.(abs (app (t ↓ (λ {A} → suc)) (var zero)))} {t′} {(abs (app u′ (var zero)))} t′t u′u (η t) = {!η t′!}  -- ok

streng-eq {Γ} {Γ′} {.(_ ⇒ _)} {i} {abs t} {abs u} {abs t′} {abs u′} t′t u′u (λcong-abs eq)
  = {!!} -- ok
-- have u′ ↓ ↑⊆ i ≡ u, same for t′, then by induction t′ ≡λ u′ and therefore abs t′ ≡ abs u′

streng-eq {Γ} {Γ′} {A} {i} {.(app _ _)} {.(app _ _)} {t′} {u′} t′t u′u (λcong-app eq eq₁) = {!!}

streng-eq {Γ} {Γ′} {A} {i} {t} {.t} {t′} {u′} t′t u′u λrefl = {!λrefl inj-ren-inj ...!}
-- needs i to be an injective renaming!

streng-eq {Γ} {Γ′} {A} {i} {t} {u} {t′} {u′} t′t u′u (λsym eq) = λsym (streng-eq u′u t′t eq)

streng-eq {Γ} {Γ′} {A} {i} {t} {u} {t′} {u′} t′t u′u (λtrans eq eq₁) = {!!}
-- need something stronger?

{- In order to prove weak completeness of Henkin models we need to construct an
   "infinite context Γ₁ ⊆ Γ₂ ⊆ ... ⊆ Γ∞. Then let
     [ A ] = { t | t : Term Δ A, Δ ⊆ Γᵢ for some i } MODULO term equality, where
   term equality is considered in the common upper bound of two terms.
   Define application to also first lift both terms to the lowest upper bound of
   their contexts.

   We show extensionality by applying both functions to a fresh variable name.
   
   From equational strengthening we get completeness -}
