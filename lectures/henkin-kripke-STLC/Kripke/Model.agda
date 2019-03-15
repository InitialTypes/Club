open import Library
open import Terms
open import STLC
open import Kripke.Semantics

open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (Extensionality; cong-app)

module Kripke.Model (K : Kripke) (funext : Extensionality 0ℓ 0ℓ) where
open Semantics′ K
open import Kripke.Soundness K

model : STLC-Model
model = record { sem = sem ;
                 soundness = λ eq hyp → funext
                                (λ w → funext (is-sound′ eq hyp)) }
