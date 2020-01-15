{-
This is the companion code for a talk at the Initial Types Club, Chalmers
University Göteborg, Feb 7 2019, by Jannis Limperg
(email: <my first name>@<my last name>.de).

Title: Proof by Reflection

Abstract:

Proof by reflection (which is only superficially related to Agda's Reflection
metaprogramming facilities) is a proof technique for dependently typed
languages. It is typically used to build solvers for a class of problems, for
example determining whether a formula of propositional logic is true. These
solvers can replace lengthy manual proofs, and they are typically more efficient
than tactics based on metaprogramming.

I will live-code the second-most boring example of proof by reflection: a
simplifier for equations in a monoid. Afterwards, I'll talk briefly about
variations on the basic technique and more interesting applications.
-}

module proof-by-reflection where

open import Relation.Binary.PropositionalEquality using
  (_≡_ ; refl ; sym ; trans ; cong ; cong-app ; module ≡-Reasoning)

open ≡-Reasoning


-- # Basic Template

{-
This section shows the implementation of a reflective solver that generates
proofs for equalities in arbitrary monoids. It does so by, essentially,
normalising both sides of the equation and checking whether the normal forms are
equal. The implementation proceeds in four steps.
-}

module Basic where

  record Monoid : Set₁ where
    field
      Carrier : Set
      zero    : Carrier
      plus    : Carrier → Carrier → Carrier

      zero-l : ∀ {x}     → plus zero x ≡ x
      zero-r : ∀ {x}     → plus x zero ≡ x
      assoc  : ∀ {x y z} → plus (plus x y) z ≡ plus x (plus y z)

  open Monoid public


  {-
  Step 1: Define a syntactic representation, `Tm`, for expressions in a monoid:

  - `𝟘` represents the monoid's zero/unit element.
  - `_+_` represents the monoid's binary operation.
  - `[ x ]` is called an uninterpreted term. Our simplifier will treat it as an
    arbitrary element of the carrier set.
  -}

  data Tm (Carrier : Set) : Set where
    [_]  : Carrier            → Tm Carrier
    𝟘    :                      Tm Carrier
    _+_  : (t u : Tm Carrier) → Tm Carrier


  {-
  Step 2: Define the denotation (meaning) of a term in a given monoid.
  -}

  tmD : (M : Monoid) → Tm (Carrier M) → Carrier M
  tmD M [ x ]   = x
  tmD M 𝟘       = zero M
  tmD M (t + u) = plus M (tmD M t) (tmD M u)


  {-
  Step 3: Define a function which simplifies a term. The simplification must
  not change the meaning of a term ('soundness'). In also shouldn't miss any
  simplification opportunities ('completeness').
  -}

  simp : ∀ {Carrier} → Tm Carrier → Tm Carrier
  simp [ x ] = [ x ]
  simp 𝟘     = 𝟘
  simp (t + u) with simp t | simp u
  ... | [ x ]    | [ y ]    = [ x ] + [ y ]
  ... | [ x ]    | 𝟘        = [ x ]
  ... | [ x ]    | su + su′ = [ x ] + (su + su′)
  ... | 𝟘        | su       = su
  ... | st + st′ | [ x ]    = st + (st′ + [ x ])
  ... | st + st′ | 𝟘        = st + st′
  ... | st + st′ | su + su′ = st + (st′ + (su + su′))

  -- The `simp` given during the talk was incomplete, as it missed a
  -- simplification opportunity. I hope that the above is now complete (but no
  -- proof!).


  {-
  Step 4: Prove that `simp` is, indeed, sound in the above sense.
  -}

  simp-correct : (M : Monoid) (t : Tm (Carrier M))
    → tmD M t ≡ tmD M (simp t)
  simp-correct M [ x ]    = refl
  simp-correct M 𝟘        = refl
  simp-correct M (t + u)
    rewrite simp-correct M t | simp-correct M u
    with simp t    | simp u
  ... | [ x ]      | [ y ]    = refl
  ... | [ x ]      | 𝟘        = zero-r M
  ... | [ x ]      | su + su′ = refl
  ... | 𝟘          | su       = zero-l M
  ... | st + st′   | [ x ]    = assoc M
  ... | st + st′   | 𝟘        = zero-r M
  ... | st + st′   | su + su′ = assoc M


  {-
  That's it! Now we can prove annoying lemmas like the following by applying
  `simp-correct` to a syntactic representation of the equation's left-hand side
  (provided that the right-hand is the normal form of the right-hand side).
  -}

  annoying : (M : Monoid) (x y z : Carrier M)
    → let open Monoid M renaming (plus to _⊕_ ; zero to O) in

      ((O ⊕ x) ⊕ y) ⊕ (z ⊕ O) ≡ x ⊕ (y ⊕ z)

  annoying M x y z = simp-correct M (((𝟘 + [ x ]) + [ y ]) + ([ z ] + 𝟘))


-- # Extensions

-- ## Symmetric Simplification

{-
`simp-correct` only works if the right-hand side of the equation is the normal
form of the left-hand side. We usually want a variation on the technique where
we only require that the left-hand side and the right-hand side have the same
normal form.
-}

module Sym where

  open Basic

  simp-correct-sym : (M : Monoid) (t u : Tm (Carrier M))
    → simp t ≡ simp u
    → tmD M t ≡ tmD M u
  simp-correct-sym M t u eq =
    begin
      tmD M t
    ≡⟨ simp-correct M t ⟩
      tmD M (simp t)
    ≡⟨ cong (tmD M) eq ⟩
      tmD M (simp u)
    ≡⟨ sym (simp-correct M u) ⟩
      tmD M u
    ∎


  more-annoying : (M : Monoid) (x y z : Carrier M)
    → let open Monoid M renaming (plus to _⊕_ ; zero to O) in

      ((O ⊕ x) ⊕ y) ⊕ (z ⊕ O) ≡ (x ⊕ y) ⊕ (z ⊕ O)

  more-annoying M x y z = simp-correct-sym M
    (((𝟘 + [ x ]) + [ y ]) + ([ z ] + 𝟘))
    (([ x ] + [ y ]) + ([ z ] + 𝟘))
    refl


-- ## Constructing Tm by Reflection

{-
So far, we have had to write syntactic representations of our terms by hand.
Given that there is a very obvious correspondence between the terms and their
syntactic counterparts, we can enlist the help of Agda's metaprogramming
facilities (confusingly also called 'reflection') to write the syntactic
representations for us. This is conceptually straightforward, but the
implementation is a bit annoying, so I only give an outline.
-}

module Reflection where

  open import Data.Unit using (⊤)
  open import Reflection using (Term ; TC)

  open Basic using (Monoid)

  macro
    simp! : Monoid → Term → TC ⊤
    simp! M hole = {!!}

  {-
  Implementation outline:

  - Infer type of `hole`.
  - Match type of `hole` with `?t ≡ ?u`, where `t, u : Carrier M`
  - Construct `T, U` such that `tmD M T ≡ t` and `tmD M U ≡ u`.
  - Fill `hole` with `simp-correct-sym M T U refl`.

  Usage:

  `more-annoying M x y z = simp! M`
  -}


-- ## Environment for Uninterpreted Terms

{-
So far, we have included uninterpreted terms in the `Tm` datatype directly. In
practice, we usually want to store them in an environment (here simply a vector)
which `Tm` indexes into. The advantage of doing so is that `Tm` then has
decidable propositional equality and a total ordering.

This is important for normalisation procedures in richer algebraic structures.
For example, in a commutative monoid, we need to decide whether the normal form
of `x + y` is `x + y` or `y + x`. One way to do so is to look at whether the
index of the uninterpreted term `x` is smaller than that of `y`.
-}

module Env where

  open import Data.Fin using (Fin)
  open import Data.Nat using (ℕ)
  open import Data.Vec using (Vec ; [] ; _∷_ ; lookup)

  open Basic using (Monoid ; Carrier ; zero ; plus)


  Env : Set → ℕ → Set
  Env = Vec


  data Tm (n : ℕ) : Set where
    [_] : Fin n → Tm n
    𝟘 : Tm n
    _+_ : (x y : Tm n) → Tm n


  tmD : (M : Monoid) → ∀ {n} → Env (Carrier M) n → Tm n → Carrier M
  tmD M Γ [ x ] = lookup Γ x
  tmD M Γ 𝟘 = zero M
  tmD M Γ (t + u) = plus M (tmD M Γ t) (tmD M Γ u)


  -- etc.


-- ## Multi-Sorted Term Language

{-
So far, our term languages have been unityped: Any term represents an element of
some monoid's carrier set. If we want to model richer problem domains, we need
to work with typed term languages instead. For example, if our language contains
descriptions of monoid homomorphisms in addition to descriptions of monoid
elements, then the term

    F x + G y

only makes sense (i.e., has a denotation) if `x` is an element of monoid `M`, `y`
is an element of monoid `N`, `F` is a homomorphism from `M` to `O` and `G` is
a homomorphism from `N` to `O`.

I don't yet know the best way to deal with these more complicated domains. I can
only report that they come with a bag of problems:

- The term language must be either intrinsically or extrinsically typed.
  Intrinsic typing is problematic for complex type systems. Extrinsic typing is
  better understood, but requires that we either write or generate a typing
  derivation when calling the reflective tactic.
- Similarly, the environments now need to be typed. They can be stratified into
  different environments for different types/sorts or implemented as telescopes.
- If the involved objects (e.g. monoids) are at different universe levels, they
  must be lifted to the maximum of all universe levels. This can be done
  manually or via metaprogramming.
-}


-- ## Composable Reflective Tactics

{-
See Gregory Malecha's papers/dissertation on 'Rtac'.

High-level overview: https://gmalecha.github.io/reflections/2016/rtac-technical-overview
-}


-- # Bonus: Monoid Normalisation Via the Free Monoid

{-
... as suggested by Andreas Abel during the talk. The free monoid over a
carrier set `C` is simply `List C`.
-}

module Free where

  open import Algebra.FunctionProperties using (Associative)
  open import Data.List using (List ; [] ; _∷_ ; _++_ ; foldr)
  open import Data.List.Properties using (foldr-++)

  open Basic using (Monoid ; module Monoid ; Tm ; 𝟘 ; _+_ ; [_] ; tmD)


  nf : ∀ {Carrier} → Tm Carrier → List Carrier
  nf [ x ] = x ∷ []
  nf 𝟘 = []
  nf (t + u) = nf t ++ nf u


  module _ (M : Monoid) where

    open Monoid M renaming (zero to O ; plus to _⊕_)


    nfD : List Carrier → Carrier
    nfD = foldr _⊕_ O


    nfD-++ : ∀ xs ys → nfD xs ⊕ nfD ys ≡ nfD (xs ++ ys)
    nfD-++ []       ys = zero-l
    nfD-++ (x ∷ xs) ys = trans assoc (cong (x ⊕_) (nfD-++ xs ys))


    nf-correct : (t : Tm Carrier) → tmD M t ≡ nfD (nf t)
    nf-correct [ x ]   = sym zero-r
    nf-correct 𝟘       = refl
    nf-correct (t + u)
      rewrite nf-correct t | nf-correct u
      = nfD-++ (nf t) (nf u)


    nf-correct-sym : (t u : Tm Carrier)
      → nf t ≡ nf u
      → tmD M t ≡ tmD M u
    nf-correct-sym t u eq
      = begin
          tmD M t
        ≡⟨ nf-correct t ⟩
          nfD (nf t)
        ≡⟨ cong nfD eq ⟩
          nfD (nf u)
        ≡⟨ sym (nf-correct u) ⟩
          tmD M u
        ∎


    more-annoying : ∀ x y z →
      ((O ⊕ x) ⊕ y) ⊕ (z ⊕ O) ≡ (x ⊕ y) ⊕ (z ⊕ O)
    more-annoying x y z = nf-correct-sym
      (((𝟘 + [ x ]) + [ y ]) + ([ z ] + 𝟘))
      (([ x ] + [ y ]) + ([ z ] + 𝟘))
      refl
