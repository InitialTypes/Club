----------------------
-- Demystifying NbE --
----------------------

-- This is the short version of the code used during the ITC talk.

-- For full version see:
--   https://github.com/nachivpn/gluetn

-- For abstract of the talk see:
--   https://github.com/InitialTypes/Club/wiki/Abstracts.2019.DemystifyingNbE

open import Data.Nat
  using (ℕ ; zero ; suc)
open import Data.Product
  using (∃ ; _×_ ; _,_)
  renaming (proj₁ to π₁ ; proj₂ to π₂)
open import Relation.Nullary
  using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star)
  renaming (_◅◅_ to trans)

open Star renaming (ε to refl)
open _≡_ renaming (refl to ≡-refl)

infixr 5 _⇒_
infixl 5 _∙_
infix  3 _⟶*_

-- Types
data Ty : Set where
  Nat : Ty
  _⇒_ : (a : Ty) → (b : Ty) → Ty

variable
  a b c : Ty

-- Terms
data Tm : Ty → Set where
  K    : Tm (a ⇒ b ⇒ a)
  S    : Tm ((a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c)
  Zero : Tm Nat
  Succ : Tm (Nat ⇒ Nat)
  Rec  : Tm (a ⇒ (Nat ⇒ a ⇒ a) ⇒ Nat ⇒ a)
  _∙_  : Tm (a ⇒ b) → Tm a → Tm b

-- Examples of terms
module _ where

  id : Tm (a ⇒ a)
  id {a} = S ∙ K ∙ K {b = a}

  plus : Tm Nat → Tm Nat → Tm Nat
  plus m n = Rec ∙ n ∙ (K ∙ Succ) ∙ m

  one = Succ ∙ Zero
  two = Succ ∙ one

  three : Tm Nat
  three = plus one two

  three' : Tm Nat
  three' = plus two one

----------------------
-- Redution relations
----------------------

-- Single-step reduction relation
data _⟶_ : Tm a → Tm a → Set where

  redk : {x : Tm a} {y : Tm b}
    → (K ∙ x ∙ y) ⟶ x

  reds : {g : Tm (a ⇒ b ⇒ c)} {f : Tm (a ⇒ b)} {x : Tm a}
    → (S ∙ g ∙ f ∙ x) ⟶ (g ∙ x ∙ (f ∙ x))

  rec0 : {b : Tm a} {f : Tm (Nat ⇒ a ⇒ a)}
    → (Rec ∙ b ∙ f ∙ Zero) ⟶ b

  recs : {b : Tm a} {f : Tm (Nat ⇒ a ⇒ a)} {n : Tm Nat}
    → (Rec ∙ b ∙ f ∙ (Succ ∙ n)) ⟶ (f ∙ n ∙ (Rec ∙ b ∙ f ∙ n))

  fun  : {t t' : Tm (a ⇒ b)} {u : Tm a}
    → t ⟶ t'
    → (t ∙ u) ⟶ (t' ∙ u)

  arg  : {t : Tm (a ⇒ b)} {u u' : Tm a}
    → u ⟶ u'
    → (t ∙ u) ⟶ (t ∙ u')

-- Multi-step (0 or more single-steps) reduction relation
_⟶*_ : Tm a → Tm a → Set
_⟶*_ = Star (_⟶_)

-- embed ⟶ to ⟶*
lift : {e e' : Tm a}
  → e ⟶ e'
  → e ⟶* e'
lift p = p ◅ refl

-- congruence rule for ∙ (in ⟶*)
cong-∙  : {t t' : Tm (a ⇒ b)} {u u' : Tm a}
    → t ⟶* t'
    → u ⟶* u'
    → t ∙ u ⟶* t' ∙ u'
cong-∙ refl    refl    = refl
cong-∙ refl    (x ◅ q) = (arg x) ◅ (cong-∙ refl q)
cong-∙ (x ◅ p) q       = (fun x) ◅ (cong-∙ p q)

-------------------------------
-- Normalization by Evaluation
-------------------------------

-- interpretation of types
⟦_⟧ : Ty → Set
⟦  Nat  ⟧ = ℕ
⟦ a ⇒ b ⟧ = Tm (a ⇒ b) × (⟦ a ⟧ → ⟦ b ⟧)

-- reify or quote semantic values to terms
quot : ⟦ a ⟧ → Tm a
quot {Nat}   zero     = Zero
quot {Nat}   (suc x)  = Succ ∙ (quot x)
quot {a ⇒ b} (t , _)  = t

infixl 5 _∘_

-- semantic application
_∘_ : ⟦ a ⇒ b ⟧ → ⟦ a ⟧ → ⟦ b ⟧
_∘_ (_ , f) x = f x

-- semantic recursion
rec' : ⟦ a ⟧ → ⟦ Nat ⇒ a ⇒ a ⟧ → ⟦ Nat ⟧ → ⟦ a ⟧
rec' b f zero = b
rec' b f (suc n) = f ∘ n ∘ (rec' b f n)

-- evaluation/interpretation of terms
eval : Tm a → ⟦ a ⟧
eval K    = K , λ x → (K ∙ (quot x)) , λ _ → x
eval S    = S , λ g
  → S ∙ (quot g) , λ f
    → S ∙ (quot g) ∙ (quot f) , λ x
      → (g ∘ x) ∘ (f ∘ x)
eval Zero = zero
eval Succ = Succ , suc
eval Rec  = Rec , λ b
  → Rec ∙ (quot b) , λ f
    → Rec ∙ (quot b) ∙ (quot f) , λ n
      → rec' b f n
eval (t ∙ u) = (eval t) ∘ (eval u)

-- normalization function
norm : Tm a → Tm a
norm t = quot (eval t)

-- Examples of normalization
module _ where

  three≈three' : norm three ≡ norm three'
  three≈three' = ≡-refl

  sillyId : Tm (a ⇒ a)
  sillyId {a} = S ∙ (K ∙ K ∙ K {a} {a}) ∙ K {_} {a}

  sillyId≈Id : norm id ≡ norm (sillyId {a})
  sillyId≈Id = ≡-refl

-------------------------------------------------------------
-- Logging the reduction trace of the normalization function
-------------------------------------------------------------

-- "Trace builder"
-- (a logical relation between terms and semantic values)
R : Tm a → ⟦ a ⟧ → Set

-- A trace builder of type `R t x` contains:
-- 1. a reduction trace t ⟶* (quote x)
-- 2. (if t has a function type)
--    a function which, given the trace builder for an argument u,
--    returns a new trace builder for its application with t

R {Nat}   t n = t ⟶* quot n
R {a ⇒ b} t f = t ⟶* quot f
  -- secret sauce (ss)
  × ({u : Tm a}{x : ⟦ a ⟧} → R u x → R (t ∙ u) (f ∘ x))

-- build/extract the trace
R-reduces : {t : Tm a} {x : ⟦ a ⟧}
  → R t x
  → t ⟶* quot x
R-reduces {Nat}   t⟶*n       = t⟶*n
R-reduces {a ⇒ b} (t⟶*f , _) = t⟶*f

-- given trace builder of function and an argument,
-- we get a trace builder for their application
R-app : {t : Tm (a ⇒ b)} {f : ⟦ a ⇒ b ⟧} {u : Tm a} {x : ⟦ a ⟧}
  → R t f
  → R u x
  → R (t ∙ u) (f ∘ x)
R-app (_ , ss) uRx = ss uRx

-- given a reduction (g ⟶* f)
-- and a trace builder `R f x`,
-- then we get trace builder `R g x`
R-chain : {f g : Tm a} {x : ⟦ a ⟧}
  → g ⟶* f
  → R f x
  → R g x
R-chain {Nat} g⟶*f f⟶*n
  = trans g⟶*f f⟶*n
R-chain {a ⇒ b} g⟶*f (f⟶*h , ss)
  = trans g⟶*f f⟶*h
  , λ {u} {y} uRy → R-chain (cong-∙ g⟶*f refl) (ss uRy)

-- trace builder for recursion
R-rec : {e : Tm a} {v : ⟦ a ⟧}
  {t : Tm (Nat ⇒ a ⇒ a)} {f : ⟦ Nat ⇒ a ⇒ a ⟧}
  {n : Tm Nat} {m : ⟦ Nat ⟧}
  → R e v
  → R t f
  → R n m
  → R (Rec ∙ e ∙ t  ∙ n) (rec' v f m)
R-rec {m = zero} p q r
  = R-chain (trans (cong-∙ refl r) (lift rec0)) p
R-rec {m = suc m} p q r
  = R-chain
      (trans (cong-∙ refl r) (lift recs))
      (R-app (R-app q refl) (R-rec {m = m} p q refl))

-- implement a trace builder for the entirety of `eval`
fund : (t : Tm a) → R t (eval t)
fund Zero = refl
fund Succ = refl , (λ x → cong-∙ refl x)
fund K = refl , (λ x
  → (cong-∙ refl (R-reduces x))
    , λ x₁ → R-chain (lift redk) x)
fund (t ∙ u) = R-app (fund t) (fund u)
fund S = refl , λ p →
  cong-∙ refl (R-reduces p) , λ q →
    (cong-∙ (cong-∙ refl (R-reduces p)) (R-reduces q)) , λ r →
      R-chain (lift reds) (R-app (R-app p r) (R-app q r))
fund Rec
  = refl , λ p →
    (cong-∙ refl (R-reduces p)) , λ q →
      (cong-∙ (cong-∙ refl (R-reduces p)) (R-reduces q)) , λ {_} {n} r →
        R-rec {m = n} p q r

-- build a trace using the trace builder from `fund`
trace : (t : Tm a) → t ⟶* norm t
trace t = R-reduces (fund t)

------------
-- Exercises
------------

-----
-- 1. Prove soundness of (multi-step) reduction
-----

--sound-red* : {t t' : Tm a} → t ⟶* t' → eval t ≡ eval t'
--sound-red* = {!!}

-----
-- 2. Show that `norm t` doesn't reduce further
-----

DoesntReduce : Tm a → Set
DoesntReduce {a} t = {t' : Tm a} → ¬ (t ⟶ t')

--nfDoesntReduce : (t : Tm a) → DoesntReduce (norm t)
--nfDoesntReduce t = {!!}

-----
-- 3. Prove weak normalization
-----

WeakNorm : Tm a → Set
WeakNorm t = ∃ λ t' → (t ⟶* t') × DoesntReduce t'

--weakNorm : ∀ (t : Tm a) → WeakNorm t
--weakNorm t = {!!}

-----
-- 4. Prove church-rosser property
-----

Converge : (t t' : Tm a) → Set
Converge t t' =  ∃ λ v → (t ⟶* v) × (t' ⟶* v)

--church-rosser : {t u u' : Tm a}
--  → t ⟶* u
--  → t ⟶* u'
--  → Converge u u'
----church-rosser p q = {!!}

-----
-- 5. Prove decidability of convergence
-----

--open import Relation.Nullary using (Dec ; yes ; no)
--
--converge? : (t t' : Tm a) → Dec (Converge t t')
--converge? t t' = {!!}
