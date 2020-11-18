------------------------------------------------------------------------
-- The internal language of CCCs forms a CCC

module CCC.Examples.Internal where

open import CCC
open import Types
import CCCInternalLanguage as Internal

Internal-CCC : CCC _ _ _
Internal-CCC = record

  { cc = record
      -- Objects and morphisms.
      { Ob   = Ty
      ; Homs = homSetoid

      -- Category operations
      ; id   = λ _ → id
      ; comp = _∘_

      -- Category laws
      ; id-l  = λ _ → id-l
      ; id-r  = λ _ → id-r
      ; assoc = λ _ _ _ → assoc

      ; comp-cong = eq-comp

      -- Product object and projections
      ; Prod = _*_
      ; π₁   = fst
      ; π₂   = snd

      -- Pairing and β-laws
      ; pair = pair
      ; β-π₁ = fst-pair
      ; β-π₂ = snd-pair

      -- Uniqueness of pairing
      ; pair-unique = pair-unique

      -- Terminal object
      ; Unit = 𝟙
      ; unit = λ _ → unit

      -- Uniqueness of terminal morphism
      ; unit-unique = λ _ → unit
      }

  -- Exponential object and application
  ; Arr  = _⇒_
  ; eval = eval

  -- Currying and the computation law for application
  ; curry        = curry
  ; β-eval       = λ _ → eval-curry

  -- Uniqueness of curry
  ; curry-unique = curry-unique
  }
  where open Internal
