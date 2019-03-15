open import Library
open import Terms
open import STLC
open import Henkin.Semantics

open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (Extensionality; cong-app)

module Henkin.Model (H : Henkin) (funext : Extensionality 0ℓ 0ℓ) where
open Semantics′ H
open import Henkin.Soundness H

model : STLC-Model
model = record { sem = sem ;
                 soundness = λ eq hyp → funext (is-sound′ eq hyp) }
