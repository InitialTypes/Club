open import Library
open import Terms
open import STLC

open import Standard.Semantics
open import Standard.Lemmas
open import Standard.Soundness

module Standard.Model where

model : STLC-Model
model = record { sem = sem ; soundness = is-sound }
