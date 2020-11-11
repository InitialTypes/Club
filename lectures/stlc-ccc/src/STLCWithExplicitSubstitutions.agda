-- Terms are intrinsically typed.
-- Terms are the typing derivations of untyped terms (which are not shown).

-- This file contains the calculus of Section 1.5 in the lecture
-- notes. For the one of Section 1.6 see
-- STLCWithExplicitSubstitutionsWithExplicitWeakening.agda.

-- For greek letters, type \ G <letter>.

open import Types

-- Syntax.

mutual

  infixl 10 _[_]

  -----------------------------------------
  -- Well-typed terms.
  -----------------------------------------

  data Tm : (Γ : Cxt) (a : Ty) → Set where

    -- Variable.

    var : ∀{Γ a}
      (n : a ∈ Γ)
      → Tm Γ a

    -- λ-abstraction.

    abs : ∀{Γ a b}
      (t : Tm (Γ , a) b)
      → Tm Γ (a ⇒ b)

    -- Application.

    app : ∀{Γ a b}
      (t : Tm Γ (a ⇒ b))
      (u : Tm Γ a)
      → Tm Γ b

    -- Explicit substitution.

    _[_] : ∀{Γ Δ a}
      (t : Tm Γ a)
      (s : Sub Δ Γ)
      → Tm Δ a

  -----------------------------------------
  -- Well-typed substitutions.
  -----------------------------------------

  infixl 2 _,_
  infixl 4 _∘_

  data Sub : (Γ Δ : Cxt) → Set where

    -- The empty substitution.

    ε : ∀{Γ}
      → Sub Γ ε

    -- Substitution extension.

    _,_ : ∀{Γ Δ a}
      (s : Sub Γ Δ)
      (t : Tm Γ a)
      → Sub Γ (Δ , a)

private
  wk^ : ∀{Δ Γ} → Γ ≼ Δ → Sub Δ Γ
  wk^ {Γ = ε}     n = ε
  wk^ {Γ = Γ , a} n = wk^ (1+ n) , var (n ⊕ 𝟘)

-- The identity substitution.

id : ∀{Γ}
  → Sub Γ Γ
id = wk^ zero

-- Substitution composition.

_∘_ : ∀{Γ Δ Φ}
  (r : Sub Δ Φ)
  (s : Sub Γ Δ)
  → Sub Γ Φ
ε       ∘ s = ε
(r , t) ∘ s = r ∘ s , t [ s ]

-- The weakening substitution.

wk : ∀{Γ a}
  → Sub (Γ , a) Γ
wk = wk^ (succ zero)

-- Equational theory.

mutual

  infix 0 _≅_ -- \cong

  -----------------------------------------
  -- Equal terms.
  -----------------------------------------

  data _≅_ : ∀ {Γ a} (t t' : Tm Γ a) → Set where

    -- β-equality.

    teq-beta : ∀{Γ a b} {t : Tm (Γ , a) b} {u : Tm Γ a}
      → app (abs t) u ≅ t [ id , u ]

    -- η-equality.

    teq-eta : ∀{Γ a b} {t : Tm Γ (a ⇒ b)}
      → t ≅ abs (app (t [ wk ]) (var 𝟘))

    -- β-equality laws for substitutions.

    teq-var-zero-s : ∀{Γ Δ a} {s : Sub Γ Δ} {u : Tm Γ a}
      → var 𝟘 [ s , u ] ≅ u

    teq-var-succ-s : ∀{Γ Δ a b} {n : b ∈ Δ} {s : Sub Γ Δ} {u : Tm Γ a}
      → var (𝟙+ n) [ s , u ] ≅ var n [ s ]

    -- Propagation of substitutions.

    teq-abs-s : ∀{Γ Δ a b} {s : Sub Γ Δ} {t : Tm (Δ , a) b}
      → (abs t) [ s ] ≅ abs (t [ s ∘ wk , var 𝟘 ])

    teq-app-s : ∀{Γ Δ a b} {s : Sub Γ Δ} {t : Tm Δ (a ⇒ b)} {u : Tm Δ a}
      → (app t u) [ s ] ≅ app (t [ s ]) (u [ s ])

    teq-sub-s : ∀{Γ Δ Φ a} {s : Sub Γ Δ} {r : Sub Δ Φ} {t : Tm Φ a}
      → (t [ r ]) [ s ] ≅ t [ r ∘ s ]

    -- Congruence closure.

    teq-var : ∀{Γ a} {n : a ∈ Γ}
      → var n ≅ var {Γ} {a} n

    teq-abs : ∀{Γ a b} {t t' : Tm (Γ , a) b}
      → t ≅ t'
      → abs t ≅ abs t'

    teq-app : ∀{Γ a b} {t t' : Tm Γ (a ⇒ b)} {u u' : Tm Γ a}
      → t ≅ t'
      → u ≅ u'
      → app t u ≅ app t' u'

    teq-sub : ∀{Γ Δ a} {s s' : Sub Γ Δ} {t t' : Tm Δ a}
      → t ≅ t'
      → t [ s ] ≅ t' [ s ]

    -- Equivalence laws (reflexivity is admissible).

    teq-sym : ∀{Γ a} {t t' : Tm Γ a}
      → t' ≅ t
      → t ≅ t'

    teq-trans : ∀{Γ a} {t u v : Tm Γ a}
      → t ≅ u
      → u ≅ v
      → t ≅ v

{- TODO: show admissible laws:

-- Reflexivity

-- Admissible identity substitution law (first functor law).

teq-sub-id : ∀{Γ a} {t : Tm Γ a}
      → t [ id ] ≅ t
teq-sub-id {t = var n} = {!!}
teq-sub-id {t = abs t} = {!!}
teq-sub-id {t = app t u} = {!!}
teq-sub-id {t = t [ s ]} = begin
   t [ s ] [ id ] ≅⟨ ? ⟩
   t [ s ] ∎

-- Need equality reasoning here.
-- To this end, I need that _≅_ is an equivalence relation.
-}
