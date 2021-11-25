On Consistency, Models, and Normalization for Intuitionistic Propositional Logic (IPL)
======================================================================================

With Application to Normalization for the Simply-Typed Lambda Calculus (STLC)

Intuitionistic Propositional Logic (negative fragment)
------------------------------------------------------

Propositions.

    A, B, C          -- meta-variable for proposition/formula
    ::= P            -- positive formula (only variable in neg. fragment)
      | ⊤            -- truth
      | A ∧ B        -- conjunction
      | A ⇒ B        -- implication

Contexts `Γ,Δ` are snoc-lists of propositions (hypotheses).

Hypothesis selection `A ∈ Γ` (de Bruijn indices).

                           A ∈ Γ
    zero --------     suc  -------
         A ∈ Γ.A           A ∈ Γ.B

Proofs / derivations `Γ ⊢ A` ("`Γ` entails `A`").

         A ∈ Γ
    hyp  -----
         Γ ⊢ A

    ⊤I   -----
         Γ ⊢ ⊤

         Γ ⊢ A    Γ ⊢ B         Γ ⊢ A₁ ∧ A₂
    ∧I   --------------    ∧Eᵢ  ------------
         Γ ⊢ A ∧ B              Γ ⊢ Aᵢ

         Γ.A ⊢ B                Γ ⊢ A ⇒ B    Γ ⊢ A
    ⇒I   ---------         ⇒E  -------------------
         Γ ⊢ A ⇒ B              Γ ⊢ B

Full IPL
--------

Propositions.

    A,B,C ::= ...
      | X            -- propositional variable
      | ⊥            -- absurdity / falsity
      | A ∨ B        -- disjunction

Additional inference rules:

                            Γ ⊢ ⊥
                        ⊥E  -----
                            Γ ⊢ C

         Γ ⊢ Aᵢ              Γ ⊢ A ∨ B   Γ.A ⊢ C   Γ.B ⊢ C
    ∨Iᵢ  ------------    ∨E  -----------------------------
         Γ ⊢ A₁ ∨ A₂        Γ ⊢ C

Negation: `¬A = (A ⇒ ⊥)`.


Consistency
-----------

- Are there propositions that are not derivable?
- Is `⊢ ⊥` not derivable?

Proof attempt:

    ...       ...        ...
    ------    -------    ---
    A ⊢ ⊥     ⊢ B ⇒ A    ⊢ B
    -------   --------------
    ⊢ A ⇒ ⊥   ⊢ A
    --------------
    ⊢ ⊥

Must every proof attempt fail?


Normal proofs
-------------

Our proof rules are more liberal than necesssary:

- Introduction followed by elimination is a detour (β)
- Negative propositions can always proven by introduction (η)

Refinement:

    Γ ⊢ A ↓   -- proof by eliminating hypothesis (neutral)
    Γ ⊢ A ⇑   -- proof by introduction (normal)

Negative fragment:

         A ∈ Γ                    Γ ⊢ P ↓
    hyp  -------              ne  -------
         Γ ⊢ A ↓                  Γ ⊢ P ⇑

    ⊤I   -------
         Γ ⊢ ⊤ ⇑

         Γ ⊢ A ⇑   Γ ⊢ B ⇑        Γ ⊢ A₁ ∧ A₂ ↓
    ∧I   -----------------    ∧Eᵢ  -------------
         Γ ⊢ A ∧ B ⇑              Γ ⊢ Aᵢ ↓

         Γ.A ⊢ B ⇑                Γ ⊢ A ⇒ B ↓   Γ ⊢ A ⇑
    ⇒I   -----------          ⇒E  -------------------
         Γ ⊢ A ⇒ B ⇑              Γ ⊢ B ↓

Positive connectives:

                            Γ ⊢ ⊥ ↓
                        ⊥E  -------
                            Γ ⊢ C ⇑

         Γ ⊢ Aᵢ ⇑              Γ ⊢ A ∨ B ↓   Γ.A ⊢ C ⇑   Γ.B ⊢ C ⇑
    ∨Iᵢ  --------------    ∨E  ------------------------------------
         Γ ⊢ A₁ ∨ A₂ ⇑        Γ ⊢ C ⇑


Normalization problem:  If `Γ ⊢ A` is derivable, then also `Γ ⊢ A ⇑`?


Consequences of normalization
-----------------------------

Consistency: There is no derivation of `⊢ ⊥ ↓/⇑`.
Proof: There is no derivation of `⊢ A ↓`.

Non-classicality: There are no closed derivations of
1. `X ∨ ¬X`             (LEM: law of excluded middle)
2. `¬¬X ⇒ X`            (RAA: _reductio ad absurdum_)
3. `((X ⇒ Y) ⇒ X) ⇒ X` (Peirce formula)


Models
======

Truthtables (Boolean model).

    ξ : Form → Bool
    ξ(A ⇒ B) = ξ(A) implies ξ(B) = not ξ(A) || ξ(B)

    ξ : Cxt → Bool
    ξ(ε)   = true
    ξ(Γ.A) = ξ(Γ) && ξ(A)

    ξ(Γ ⊢ A) = ξ(Γ) implies ξ(A)

Validates all inference rules, but also LEM etc.

Problem: _material_ implication:
- `A ⇒ B` is true when either `B` happens to be true or `A` happens to be false
- no real causality


Kripke models
-------------

Purpose: model intuitionistic implication.

Parametrized by:

1. Preordered set of worlds `(W,≤)`.
   Relation `w' ≤ w` (often `w' ⊇ w`) means `w'` is future of `w`.
  (Direction of `≤` inspired by presheaf models and subtyping.)

2. Valuation `⟦X⟧w` of the propositional variables in each world.
   Must be monotone: `⟦X⟧w` implies `⟦X⟧w'` whenever `w' ≤ w`.

Interpretation of formula `⟦A⟧w` (extended from `⟦X⟧w`):

- `⟦⊤⟧w` always.
- `⟦A ∧ B⟧w` iff `⟦A⟧w` and `⟦B⟧w`.
- `⟦A ⇒ B⟧w` iff `⟦A⟧w'` implies `⟦B⟧w'` for all `w' ≤ w`.
- `⟦⊥⟧w` never.
- `⟦A ∨ B⟧w` iff `⟦A⟧w` or `⟦B⟧w`.


Application of Kripke models: IPL is non-classical
--------------------------------------------------

Refutation of `X ∨ ¬X` with `W` given by `{X} ⊇ {}`.
1. `⟦X⟧{}` is false.
2. `⟦X ⇒ ⊥⟧{}` is false because looking at future `{X}`:
   `⟦X ⇒ ⊥⟧{X}` is false, because:
   - `⟦X⟧{X}` is true and
   - `⟦⊥⟧{X}` is false.

Theorem (monotonicity): `⟦A⟧w` implies `⟦A⟧w'` whenever `w' ≤ w`.

Theorem (soundness): In any Kripke model,
if `Γ ⊢ A` then `⟦Γ⟧w` implies `⟦A⟧w` in any world `w`.

Corollary (LEM not derivable): `⊢ X ∨ ¬X` is false.

Exercise: prove these theorems, refute the other classical principles.

Question: We refuted LEM by normalization and by Kripke models.
Are these methods related?


Completeness
------------

Let `Γ ⊧ A` mean that in any Kripke model and world `w`,
`⟦Γ⟧w` implies `⟦A⟧w`.

Soundness (reformulated):  `Γ ⊢ A` implies `Γ ⊧ A`.

Theorem (Completeness): If `Γ ⊧ A`, then `Γ ⊢ A ⇑`.

We employ the _universal model_ where
- worlds are contexts `Δ` and
- `Δ' ≤ Δ` if `Δ` is a sublist of `Δ'`
  (written `Δ' ⊇ Δ` by abuse of notation).
- `⟦X⟧Δ` iff `Δ ⊢ X ↓` (neutral proof)
- `⟦X⟧` is monotone because derivations are closed under thinning

Lemma (for negative `A`, mutual by induction on `A`):
1. Reflection (unquote): if `Δ ⊢ A ↓` then `⟦A⟧Δ`.
2. Reification (quote): if `⟦A⟧Δ` then `Δ ⊢ A ⇑`.

Lemma (Identity, by induction on `Γ`): `⟦Γ⟧Γ`.

Proof of Completeness:
Instantiating `Γ ⊧ A` to the universal model,
we have `⟦A⟧Γ` by Identity, thus `Γ ⊢ A ⇑` by reification.


Normalization
-------------

If `Γ ⊢ A`, then `Γ ⊧ A` by Soundness, and `Γ ⊢ A ⇑` by Completeness.

This argument is constructive for the negative fragment of IPL, so we
can get a normalizer by implementing this in e.g. Agda.


Positive Connectives
====================

Identity fails for positive connectives e.g. for `⟦A ∨ B⟧(A∨B)` or `⟦⊥⟧⊥`:

    ⟦A ∨ B⟧(A∨B)  iff  ⟦A⟧(A∨B) or ⟦B⟧(A∨B)
    ⟦⊥⟧⊥ never

Need a refinement of our model.
