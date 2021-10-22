module free-monoids
  (X : Set)
  where

-- Variation of `combinatory-system-t.agda` (Nachi, 2019,
-- [Demystifying NbE](https://github.com/InitialTypes/Club/wiki/Abstracts.2019.DemystifyingNbE))
-- for the theory of monoids over a collection `X` of generators or
-- primitive operations (maybe think `print (s : String) : Unit` but
-- uninterpreted, nullary and unityped).

open import free-monoids.theory        X -- terms and equational theory
open import free-monoids.normal-form   X
open import free-monoids.model         X -- monoids
open import free-monoids.normalization X
