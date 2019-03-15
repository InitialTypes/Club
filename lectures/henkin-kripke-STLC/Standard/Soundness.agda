open import Library
open import Terms
open import STLC

open import Standard.Semantics
open import Standard.Lemmas

module Standard.Soundness where
open βη-Equality

is-sound : STLC-Properties.soundness sem
is-sound {Γ = Γ} (β t u) hyp
  rewrite sub-den t (sub u) |
          sub-weaken {Γ} id |
          id-weak-den {Γ} = refl
is-sound (η {Γ} {A} t) hyp
  rewrite weak-den {Δ = Γ , A} t suc |
          lift-weak-den {Γ} {Γ} {A} id |
          id-weak-den {Γ}
          = refl
is-sound (axiom t u i x) hyp
  rewrite weak-den t i |
          weak-den u i |
          hyp x = refl
is-sound (λcong-abs eq) hyp
  rewrite is-sound eq hyp
          = refl
is-sound (λcong-app eq eq′) hyp
  rewrite is-sound eq hyp |
          is-sound eq′ hyp
          = refl
is-sound λrefl hyp = refl
is-sound (λsym eq) hyp
  rewrite is-sound eq hyp
          = refl
is-sound (λtrans eq eq′) hyp
  rewrite is-sound eq hyp |
          is-sound eq′ hyp
          = refl
