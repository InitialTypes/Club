module UcwfExpSub where

{-

1.

Define the calculus of explicit substitutions based on the Ucwf record in Ucwf.agda

using two recursive data types for terms and substitutions

2.

Define two equality relations for terms and substitutions and make sure they are equivalence
(reflexivity can be derived)

Give setoid instances for the equality relations for terms and substitutions

3.

Give an instance of the Ucwf record using your implementation

4.

Prove the following derived laws from the axiomatization using equational reasoning on the setoid

(a) empty substitution

∀ {m} (ρ : Sub m 0) → ρ ≈ <>

(b) surjective pairing

∀ {n m} (ts : Sub m (1 + n)) → ts ≋ < p ∘ ts , q [ ts ] >

(c) lifting and extending distributes over composition (see Ucwf record for ⇑)

∀ {m n k} (γ : Sub m n) (γ' : Sub k m) → ⇑ γ ∘ ⇑ γ' ≋ ⇑ (γ ∘ γ')

5.

Extend the set of Terms to include lambdas and applications and beta-eta laws


-}
