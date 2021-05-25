{-# OPTIONS --postfix-projections #-}

-- Parametricity for predicative System F
---------------------------------------------------------------------------

-- reverse         : forall a . [a] → [a]
-- reverse-natural : reverse . map f = map f . reverse

-- Literature:

-- John C. Reynolds:
-- Types, Abstraction and Parametric Polymorphism.
-- IFIP Congress 1983: 513-523

-- Wadler, Theorems for free

open import Level renaming (zero to lzero; suc to lsuc)

open import Data.Empty                            using (⊥; ⊥-elim)

open import Data.List.Base                        using (List; []; _∷_)
open import Data.List.Relation.Unary.Any          using (Any; here; there)
open import Data.List.Membership.Propositional    using (_∈_)

open import Data.Nat.Base                         using (ℕ; zero; suc)
open import Data.Nat.GeneralisedArithmetic        using (fold)

open import Data.Product                          using (∃; _×_; _,_; proj₁; proj₂; <_,_>; map₁; map₂)
open import Data.Unit.Polymorphic                 using (⊤; tt)

open import Function.Base                         using (id; _∘_)
open import Function.Equality                     using (_⇨_)

open import Relation.Binary                       using (REL; Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Axiom.Extensionality.Propositional    using (Extensionality)

open Setoid using (Carrier; _≈_)

pattern here! = here refl

-- Predicative System F
-- ========================================================================

-- System F extends the simply typed lambda calculus by parametric
-- polymorphism.  The new type former is `∀X.A` which binds type
-- variable `X` in type `A`.  A polymorphic term `t : ∀X.A` can be
-- instantiated to any type `B`, yielding `t B : A[X=B]`.

-- Predicative F stratifies the types into a hierarchy such that
-- instantiation is well-founded.  Each type and each type variable
-- is assigned a level `l ∈ ℕ`, and type variables `X` can only be
-- instantiated with a type of the same level.
-- The level of the polymorphic type `∀X.A` is strictly greater than
-- the level of `X`, this means non-wellfounded instantiation such as
-- replacing `X` by `∀X.A` is forbidden.

-- While impredicative System F can only be modelled in an impredicative
-- meta-theory, we can model predicative F in Agda by mapping types of
-- level `l` to elements of `Set l`, i.e., sets of size `l`.
-- It is thus convenient to use Agda's builtin `Level`s for stratifying
-- System F, rather than `ℕ`.  (Of course, we could also define an injection
-- `ℕ → Level`, but since we never case on a level, this indirection is not
-- necessary.  Plus, we may profit from the constraint solver for levels.)

-- Kinding contexts
-------------------

-- As we will use nameless-syntax, a kinding context `Δ = ..., X:★ₙ, ..., Y:★ₘ, ...`
-- is simply represented by a list of levels `..., n, ..., m, ...`.

KCxt = List Level

variable
  k l : Level
  Δ Δ' Δ₁ Δ₂ Δ₃ : KCxt

-- Types
--------

-- A,B ::= X | A → B | ∀(X : ★ₙ). A

-- Δ = ... X:★ₙ ...
-- Δ ⊢ A : ★ₙ
-- A : (Δ ⊢ ★ₙ)

--   Δ, X : ★ₖ ⊢ A : ★ₗ
--   ------------------------------
--   Δ ⊢ ∀ (X:★ₖ).A : ★(max(k+1,l))

mutual

  -- Types with a explicit substitution constructor A[τ]

  data Ty : (Δ : KCxt) (k : Level) → Set where
    var  :                               Ty (k ∷ Δ) k
    _⇒_  : (A : Ty Δ k) (B : Ty Δ l)   → Ty Δ (k ⊔ l)
    ∀̇    : (A : Ty (k ∷ Δ) l)          → Ty Δ (lsuc k ⊔ l)
    _[_] : (A : Ty Δ l) (τ : Sub Δ' Δ) → Ty Δ' l

  -- (Parallel) substitutions.
  -- `τ : Sub Δ Δ'` provides a type `Ty Δ k` for each `k ∈ Δ'`.
  --
  -- The chosen forms make it easy to define singleton substitutions (`sgS`)
  -- and lifting a substitution under a binder (`liftS`).
  -- The empty substitution is a sequence of `wkS` on `idS`.
  -- Composition of substitution could be defined recursively,
  -- but we don't require it.

  data Sub : (Δ Δ' : KCxt) → Set where
    idS   : Sub Δ Δ
    wkS   : (τ : Sub Δ Δ') → Sub (k ∷ Δ) Δ'
    extS  : (A : Ty  Δ k) (τ : Sub Δ Δ') → Sub Δ (k ∷ Δ')

infixr 6 _⇒_
infixl 10 _[_]

variable
  A A' A'' B B' : Ty Δ k
  S S'          : Set k
  τ τ'          : Sub Δ Δ'

-- Derived type constructors

Wk : Ty Δ l → Ty (k ∷ Δ) l
Wk A = A [ wkS idS ]

Var : (X : k ∈ Δ) → Ty Δ k
Var here!     = var
Var (there X) = Wk (Var X)

-- Derived substitutions

sgS : Ty Δ k → Sub Δ (k ∷ Δ)
sgS A = extS A idS

liftS : (τ : Sub Δ Δ') → Sub (k ∷ Δ) (k ∷ Δ')
liftS τ = extS var (wkS τ)

-- Standard model for types: sets
---------------------------------

-- The maximum level in a kinding context.

⟨_⟩ : KCxt → Level
⟨ [] ⟩     = lzero
⟨ l ∷ ls ⟩ = l ⊔ ⟨ ls ⟩

-- Type environments  ξ : ⟪ Δ ⟫

⟪_⟫ : (Δ : KCxt) → Set (lsuc ⟨ Δ ⟩)
⟪ []     ⟫ = ⊤
⟪ l ∷ ls ⟫ = Set l × ⟪ ls ⟫

-- Type interpretation

mutual

  ⟦_⟧ : (A : Ty Δ k) (ξ : ⟪ Δ ⟫) → Set k
  ⟦ var     ⟧   = proj₁
  ⟦ A ⇒ B   ⟧ ξ = ⟦ A ⟧ ξ → ⟦ B ⟧ ξ
  ⟦ ∀̇ A     ⟧ ξ = ∀ S → ⟦ A ⟧ (S , ξ)
  ⟦ A [ τ ] ⟧   = ⟦ A ⟧ ∘ ⟦ τ ⟧S

  ⟦_⟧S : (τ : Sub Δ Δ') → ⟪ Δ ⟫ → ⟪ Δ' ⟫
  ⟦ idS        ⟧S = id
  ⟦ extS A τ   ⟧S = < ⟦ A ⟧ , ⟦ τ ⟧S >
  ⟦ wkS τ      ⟧S = ⟦ τ ⟧S ∘ proj₂

-- Extensional equality on sets: setoids (UNUSED)
-------------------------------------------------

-- The following interpretation of types as setoids is naive,
-- but luckily we do not need it in the end.

E⟪_⟫ : (Δ : KCxt) → Set (lsuc ⟨ Δ ⟩)
E⟪ []     ⟫ = ⊤
E⟪ l ∷ ls ⟫ = Setoid l l × E⟪ ls ⟫

-- Just quantifying over setoids to interpret `∀` is quite crude,
-- we should at least quotient this by proof irrelevance for the laws...

module _ (open Setoid) (open IsEquivalence) where

  Π : (Setoid k k → Setoid l l) → Setoid (lsuc k ⊔ l) (lsuc k ⊔ l)
  Π F .Carrier       = ∀ S → F S .Carrier
  Π F ._≈_ f f'      = ∀ S → F S ._≈_ (f S) (f' S)
  Π F .isEquivalence .IsEquivalence.refl S = F S .Setoid.refl
  Π F .isEquivalence .sym              f S = F S .Setoid.sym (f S)
  Π F .isEquivalence .trans          f g S = F S .Setoid.trans (f S) (g S)

-- Type interpretation

mutual

  E⟦_⟧ : (A : Ty Δ k) (ξ : E⟪ Δ ⟫) → Setoid k k
  E⟦ var     ⟧   = proj₁
  E⟦ A ⇒ B   ⟧ ξ = E⟦ A ⟧ ξ ⇨ E⟦ B ⟧ ξ
  E⟦ ∀̇ A     ⟧ ξ = Π λ (S : Setoid _ _) → E⟦ A ⟧ (S , ξ)
  E⟦ A [ τ ] ⟧   = E⟦ A ⟧ ∘ E⟦ τ ⟧S

  E⟦_⟧S : (τ : Sub Δ Δ') → E⟪ Δ ⟫ → E⟪ Δ' ⟫
  E⟦ idS        ⟧S = id
  E⟦ extS A τ   ⟧S = < E⟦ A ⟧ , E⟦ τ ⟧S >
  E⟦ wkS τ      ⟧S = E⟦ τ ⟧S ∘ proj₂


-- Conversion
-------------

-- We need to propagate substitutions in order to define concrete term.
-- The relation A ↦ A' is weak-head reduction for explicit substitutions.

infix 1 _↦_

data _↦_ : (A A' : Ty Δ k) → Set where
  idS    :  A [ idS ]                 ↦ A
  compS  :  A [ wkS τ ] [ extS B τ' ] ↦ A [ τ ] [ τ' ]
  prjS   :  var [ extS A τ ]          ↦ A
  arrS   :  (A ⇒ B) [ τ ]             ↦ A [ τ ] ⇒ B [ τ ]
  allS   :  (∀̇ A) [ τ ]               ↦ ∀̇ (A [ liftS τ ])

  explS  :  A ↦ A' → A [ τ ] ↦ A' [ τ ]

-- Extending weak-head reduction to standard reduction, a structured variant of full reduction.

infix 1 _→s_

data _→s_ : (A A' : Ty Δ k) → Set where

  refl : A →s A
  step : A ↦ A' → A' →s A'' → A →s A''

  arr  : A →s A' → B →s B' → (A ⇒ B) →s (A' ⇒ B')
  all  : A →s A' → ∀̇ A →s ∀̇ A'
  expl : A →s A' → A [ τ ] →s A' [ τ ]

-- Standard model of a conversion is the identity function.

-- However, we cannot easily express this, so a conversion
-- from `A` to `A'` will simply be a pair of functions
-- `f : ⟦A⟧ → ⟦A'⟧` and `g : ⟦A'⟧ → ⟦A⟧`.

mutual

  ⦅_⦆W : {A A' : Ty Δ k} (w : A ↦ A') (ξ : ⟪ Δ ⟫) → ⟦ A ⟧ ξ → ⟦ A' ⟧ ξ
  ⦅ idS     ⦆W ξ = id
  ⦅ compS   ⦆W ξ = id
  ⦅ prjS    ⦆W ξ = id
  ⦅ arrS    ⦆W ξ = id
  ⦅ allS    ⦆W ξ = id
  ⦅ explS w ⦆W ξ = ⦅ w ⦆W _

  ⦅_⦆W⁻ : {A A' : Ty Δ k} (w : A ↦ A') (ξ : ⟪ Δ ⟫) → ⟦ A' ⟧ ξ → ⟦ A ⟧ ξ
  ⦅ idS     ⦆W⁻ ξ = id
  ⦅ compS   ⦆W⁻ ξ = id
  ⦅ prjS    ⦆W⁻ ξ = id
  ⦅ arrS    ⦆W⁻ ξ = id
  ⦅ allS    ⦆W⁻ ξ = id
  ⦅ explS w ⦆W⁻ ξ = ⦅ w ⦆W⁻ _

mutual

  ⦅_⦆S : {A A' : Ty Δ k} (s : A →s A') (ξ : ⟪ Δ ⟫) → ⟦ A ⟧ ξ → ⟦ A' ⟧ ξ
  ⦅ refl     ⦆S ξ   = id
  ⦅ step w s ⦆S ξ   = ⦅ s ⦆S ξ ∘ ⦅ w ⦆W ξ
  ⦅ arr s s' ⦆S ξ f = ⦅ s' ⦆S ξ ∘ f ∘ ⦅ s ⦆S⁻ ξ
  ⦅ all s    ⦆S ξ f = ⦅ s ⦆S _ ∘ f
  ⦅ expl s   ⦆S ξ   = ⦅ s ⦆S _

  ⦅_⦆S⁻ : {A A' : Ty Δ k} (s : A →s A') (ξ : ⟪ Δ ⟫) → ⟦ A' ⟧ ξ → ⟦ A ⟧ ξ
  ⦅ refl     ⦆S⁻ ξ   = id
  ⦅ step w s ⦆S⁻ ξ   = ⦅ w ⦆W⁻ ξ ∘ ⦅ s ⦆S⁻ ξ
  ⦅ arr s s' ⦆S⁻ ξ f = ⦅ s' ⦆S⁻ ξ ∘ f ∘ ⦅ s ⦆S ξ
  ⦅ all s    ⦆S⁻ ξ f = ⦅ s ⦆S⁻ _ ∘ f
  ⦅ expl s   ⦆S⁻ ξ   = ⦅ s ⦆S⁻ _

-- Typing contexts
------------------

-- Typing contexts `Γ` are essentially lists of types
-- with free type variables in `Δ`.
--
-- However, for the sake of a smooth definition of context interpretation
-- we add an explicit substitution constructor also to contexts.

data Cxt : (Δ : KCxt) → Set where
  []     : Cxt Δ
  _∷_    : (A : Ty Δ k) (Γ : Cxt Δ) → Cxt Δ
  _[_]G  : (Γ : Cxt Δ) (τ : Sub Δ' Δ) → Cxt Δ'

variable
  Γ Γ' : Cxt Δ

-- Weakening a context by one more type variable is then a simple abbreviation:

wkG : Cxt Δ → Cxt (k ∷ Δ)
wkG Γ  = Γ [ wkS idS ]G

-- Membership of a type in a typing context.

data _∈G_ : (A : Ty Δ k) (Γ : Cxt Δ) → Set where
  here  : A ∈G (A ∷ Γ)
  there : (x : A ∈G Γ) → A ∈G (B ∷ Γ)
  _[_]x : (x : A ∈G Γ) (τ : Sub Δ Δ') → (A [ τ ]) ∈G (Γ [ τ ]G)

-- Standard interpretation of typing contexts
---------------------------------------------------------------------------

-- The level of a typing context is the maximum level of a type
-- in that context.

⟨_⟩G : (Γ : Cxt Δ) → Level
⟨ []              ⟩G = lzero
⟨ _∷_ {k = k} A Γ ⟩G = k ⊔ ⟨ Γ ⟩G
⟨ Γ [ _ ]G        ⟩G = ⟨ Γ ⟩G

-- Environments `η : ⟦Γ⟧ξ` are tuples of values of their respective type.

⟦_⟧G : (Γ : Cxt Δ) → ⟪ Δ ⟫ → Set ⟨ Γ ⟩G
⟦ []       ⟧G ξ = ⊤
⟦ A ∷ Γ    ⟧G ξ = ⟦ A ⟧ ξ × ⟦ Γ ⟧G ξ
⟦ Γ [ τ ]G ⟧G   = ⟦ Γ ⟧G ∘ ⟦ τ ⟧S

-- Looking up the value of a variable in an environment.

⦅_⦆x : {Γ : Cxt Δ} (x : A ∈G Γ) (ξ : ⟪ Δ ⟫) (η : ⟦ Γ ⟧G ξ) → ⟦ A ⟧ ξ
⦅ here     ⦆x ξ = proj₁
⦅ there x  ⦆x ξ = ⦅ x ⦆x ξ ∘ proj₂
⦅ x [ τ ]x ⦆x   = ⦅ x ⦆x ∘ ⟦ τ ⟧S


-- Context conversion
---------------------

-- Propagating explicit substitutions on contexts.
-- UNUSED, so it may not be well engineered.

infix 1 _↦G_

data _↦G_ : (Γ Γ' : Cxt Δ) → Set where

  nil   : []      [ τ ]G  ↦G  []
  cons  : (A ∷ Γ) [ τ ]G  ↦G  A [ τ ] ∷ Γ [ τ ]G

  here  : A ↦ A'   →  A ∷ Γ    ↦G A' ∷ Γ
  there : Γ ↦G Γ'  →  A ∷ Γ    ↦G A ∷ Γ'
  explS : Γ ↦G Γ'  →  Γ [ τ ]G ↦G Γ' [ τ ]G

⦅_⦆GW : {Γ Γ' : Cxt Δ} (w : Γ ↦G Γ') (ξ : ⟪ Δ ⟫) → ⟦ Γ ⟧G ξ → ⟦ Γ' ⟧G ξ
⦅ nil     ⦆GW ξ = id
⦅ cons    ⦆GW ξ = id
⦅ here  w ⦆GW ξ = map₁ (⦅ w ⦆W ξ)
⦅ there w ⦆GW ξ = map₂ (⦅ w ⦆GW ξ)
⦅ explS w ⦆GW ξ = ⦅ w ⦆GW _

-- Terms
--------

-- Δ;Γ ⊢ t : A   where Δ ⊢ A : ★ₙ and Δ ⊢ Γ

-- need context weakening and type substitution

data Tm : ∀ {Δ : KCxt} (Γ : Cxt Δ) {k} → Ty Δ k → Set where

  var   : (x : A ∈G Γ)                          → Tm Γ A
  abs   : (t : Tm (A ∷ Γ) B)                    → Tm Γ (A ⇒ B)
  app   : (t : Tm Γ (A ⇒ B)) (u : Tm Γ A)       → Tm Γ B

  -- Generalization:
  -- ΛX:★ₙ.t : ∀X:★ₙ.A  when t : A
  -- Δ; Γ ⊢ ΛX:★ₙ.t : ∀X:★ₙ.A   when Δ,X:★ₙ; Γ ⊢ t : A  and X ∉ FV(Γ)

  gen   : (t : Tm (wkG Γ) A)                    → Tm Γ (∀̇ A)

  -- Instantiation:
  -- t B : A[B/X]  when  t : ∀X:★ₙ.A  and B : ★ₙ

  inst  : (t : Tm Γ (∀̇ {k = k} A)) (B : Ty Δ k) → Tm Γ (A [ sgS B ])

  conv  : (s : A →s A') (t : Tm Γ A)            → Tm Γ A'
  convG : (t : Tm Γ' A) (w : Γ ↦G Γ')           → Tm Γ A
  wk    : (t : Tm Γ B)                          → Tm (A ∷ Γ) B
  wkTy  : (t : Tm Γ A)                          → Tm (wkG {k = k} Γ) (Wk A)


-- Standard model of terms (functions)

⦅_⦆ : {Γ : Cxt Δ} (t : Tm Γ A) (ξ : ⟪ Δ ⟫) (η : ⟦ Γ ⟧G ξ) → ⟦ A ⟧ ξ
⦅ var x     ⦆       = ⦅ x ⦆x
⦅ abs t     ⦆ ξ η a = ⦅ t ⦆  ξ (a , η)
⦅ app t u   ⦆ ξ η   = ⦅ t ⦆  ξ       η (⦅ u ⦆ ξ η)
⦅ gen t     ⦆ ξ η S = ⦅ t ⦆  (S , ξ) η
⦅ inst t B  ⦆ ξ η   = ⦅ t ⦆  ξ       η (⟦ B ⟧ ξ)
⦅ conv s t  ⦆ ξ     = ⦅ s ⦆S ξ ∘ ⦅ t ⦆ ξ
⦅ convG t w ⦆ ξ     = ⦅ t ⦆ ξ ∘ ⦅ w ⦆GW ξ
⦅ wk t      ⦆ ξ     = ⦅ t ⦆ ξ ∘ proj₂
⦅ wkTy t    ⦆       = ⦅ t ⦆ ∘ proj₂


-- Relational model in sets
---------------------------

⟪_⟫R : (Δ : KCxt) (ξ ξ' : ⟪ Δ ⟫) → Set (lsuc ⟨ Δ ⟩)
⟪ []    ⟫R _       _         = ⊤
⟪ k ∷ Δ ⟫R (S , ξ) (S' , ξ') = REL S S' k × ⟪ Δ ⟫R ξ ξ'

-- Relational interpretation of types

-- REL S T k = S → T → Set k

mutual

  ⟦_⟧R : (A : Ty Δ k) {ξ ξ' : ⟪ Δ ⟫} (ρ : ⟪ Δ ⟫R ξ ξ') → REL (⟦ A ⟧ ξ) (⟦ A ⟧ ξ') k

  ⟦ var     ⟧R         = proj₁

  ⟦ A ⇒ B   ⟧R ρ f f'  = ∀ {a a'}
                       → ⟦ A ⟧R ρ a a'
                       → ⟦ B ⟧R ρ (f a) (f' a')

  -- ⟦★ₖ⟧ S S' = REL S S' k

  ⟦ ∀̇ A     ⟧R ρ f f'  = ∀ {S S'} (R : REL S S' _)
                       → ⟦ A ⟧R (R , ρ) (f S) (f' S')

  ⟦ A [ τ ] ⟧R         = ⟦ A ⟧R ∘ ⟦ τ ⟧SR

  ⟦_⟧SR : (τ : Sub Δ Δ') {ξ ξ' : ⟪ Δ ⟫} (ρ : ⟪ Δ ⟫R ξ ξ') → ⟪ Δ' ⟫R (⟦ τ ⟧S ξ) (⟦ τ ⟧S ξ')
  ⟦ idS      ⟧SR   = id
  ⟦ wkS τ    ⟧SR   = ⟦ τ ⟧SR ∘ proj₂
  ⟦ extS A τ ⟧SR ρ = ⟦ A ⟧R ρ , ⟦ τ ⟧SR ρ


-- Relation interpretation of conversion

mutual

  ⦅_⦆WR : {A A' : Ty Δ k} (w : A ↦ A') {ξ ξ' : ⟪ Δ ⟫} (ρ : ⟪ Δ ⟫R ξ ξ')
       → ∀ {a a'} → ⟦ A ⟧R ρ a a' → ⟦ A' ⟧R ρ (⦅ w ⦆W ξ a) (⦅ w ⦆W ξ' a')
  ⦅ idS     ⦆WR ρ = id
  ⦅ compS   ⦆WR ρ = id
  ⦅ prjS    ⦆WR ρ = id
  ⦅ arrS    ⦆WR ρ = id
  ⦅ allS    ⦆WR ρ = id
  ⦅ explS w ⦆WR ρ = ⦅ w ⦆WR _

  ⦅_⦆WR⁻ : {A A' : Ty Δ k} (w : A ↦ A') {ξ ξ' : ⟪ Δ ⟫} (ρ : ⟪ Δ ⟫R ξ ξ')
       → ∀ {a a'} → ⟦ A' ⟧R ρ a a' → ⟦ A ⟧R ρ (⦅ w ⦆W⁻ ξ a) (⦅ w ⦆W⁻ ξ' a')
  ⦅ idS     ⦆WR⁻ ρ = id
  ⦅ compS   ⦆WR⁻ ρ = id
  ⦅ prjS    ⦆WR⁻ ρ = id
  ⦅ arrS    ⦆WR⁻ ρ = id
  ⦅ allS    ⦆WR⁻ ρ = id
  ⦅ explS w ⦆WR⁻ ρ = ⦅ w ⦆WR⁻ _

mutual

  ⦅_⦆SR : {A A' : Ty Δ k} (s : A →s A') {ξ ξ' : ⟪ Δ ⟫} (ρ : ⟪ Δ ⟫R ξ ξ')
       → ∀ {a a'} → ⟦ A ⟧R ρ a a' → ⟦ A' ⟧R ρ (⦅ s ⦆S ξ a) (⦅ s ⦆S ξ' a')
  ⦅ refl     ⦆SR ρ   = id
  ⦅ step w s ⦆SR ρ   = ⦅ s ⦆SR ρ ∘ ⦅ w ⦆WR ρ
  ⦅ arr s s' ⦆SR ρ f = ⦅ s' ⦆SR ρ ∘ f ∘ ⦅ s ⦆SR⁻ ρ
  ⦅ all s    ⦆SR ρ f = ⦅ s ⦆SR _ ∘ f
  ⦅ expl s   ⦆SR ρ   = ⦅ s ⦆SR _

  ⦅_⦆SR⁻ : {A A' : Ty Δ k} (s : A →s A') {ξ ξ' : ⟪ Δ ⟫} (ρ : ⟪ Δ ⟫R ξ ξ')
       → ∀ {a a'} → ⟦ A' ⟧R ρ a a' → ⟦ A ⟧R ρ (⦅ s ⦆S⁻ ξ a) (⦅ s ⦆S⁻ ξ' a')
  ⦅ refl     ⦆SR⁻ ρ   = id
  ⦅ step w s ⦆SR⁻ ρ   = ⦅ w ⦆WR⁻ ρ ∘ ⦅ s ⦆SR⁻ ρ
  ⦅ arr s s' ⦆SR⁻ ρ f = ⦅ s' ⦆SR⁻ ρ ∘ f ∘ ⦅ s ⦆SR ρ
  ⦅ all s    ⦆SR⁻ ρ f = ⦅ s ⦆SR⁻ _ ∘ f
  ⦅ expl s   ⦆SR⁻ ρ   = ⦅ s ⦆SR⁻ _

-- Relational interpretation of contexts

⟦_⟧GR : (Γ : Cxt Δ) {ξ ξ' : ⟪ Δ ⟫} (ρ : ⟪ Δ ⟫R ξ ξ') → REL (⟦ Γ ⟧G ξ) (⟦ Γ ⟧G ξ') ⟨ Γ ⟩G
⟦ []       ⟧GR ρ _ _               = ⊤
⟦ A ∷ Γ    ⟧GR ρ (a , η) (a' , η') = ⟦ A ⟧R ρ a a'  ×  ⟦ Γ ⟧GR ρ η η'
⟦ Γ [ τ ]G ⟧GR                     = ⟦ Γ ⟧GR ∘ ⟦ τ ⟧SR


⦅_⦆GWR : {Γ Γ' : Cxt Δ} (w : Γ ↦G Γ') {ξ ξ' : ⟪ Δ ⟫} (ρ : ⟪ Δ ⟫R ξ ξ')
     → ∀ {η η'} → ⟦ Γ ⟧GR ρ η η' → ⟦ Γ' ⟧GR ρ (⦅ w ⦆GW ξ η) (⦅ w ⦆GW ξ' η')
⦅ nil     ⦆GWR ρ = id
⦅ cons    ⦆GWR ρ = id
⦅ here  w ⦆GWR ρ = map₁ (⦅ w ⦆WR ρ)
⦅ there w ⦆GWR ρ = map₂ (⦅ w ⦆GWR ρ)
⦅ explS w ⦆GWR ρ = ⦅ w ⦆GWR _


-- Fundamental theorem of logical relations for variables

⦅_⦆xR : {Γ : Cxt Δ} {A : Ty Δ k}       (x : A ∈G Γ)
       {ξ : ⟪ Δ ⟫  } {ξ' : ⟪ Δ ⟫   }  (ρ  : ⟪ Δ ⟫R ξ ξ')
       {η : ⟦ Γ ⟧G ξ} {η' : ⟦ Γ ⟧G ξ'} (rs : ⟦ Γ ⟧GR ρ η η')

     → ⟦ A ⟧R ρ (⦅ x ⦆x ξ η) (⦅ x ⦆x ξ' η')

⦅ here     ⦆xR ρ = proj₁
⦅ there x  ⦆xR ρ = ⦅ x ⦆xR ρ ∘ proj₂
⦅ x [ τ ]x ⦆xR   = ⦅ x ⦆xR ∘ ⟦ τ ⟧SR

-- Fundamental theorem of logical relations

⦅_⦆R : {Γ : Cxt Δ}    {A : Ty Δ k}      (t : Tm Γ A)
       {ξ : ⟪ Δ ⟫  }  {ξ' : ⟪ Δ ⟫   }   (ρ  : ⟪ Δ ⟫R ξ ξ')
       {η : ⟦ Γ ⟧G ξ} {η' : ⟦ Γ ⟧G ξ'}  (rs : ⟦ Γ ⟧GR ρ η η')

    → ⟦ A ⟧R ρ (⦅ t ⦆ ξ η) (⦅ t ⦆ ξ' η')

⦅ var x     ⦆R        = ⦅ x ⦆xR
⦅ abs t     ⦆R ρ rs r = ⦅ t ⦆R ρ (r , rs)
⦅ app t u   ⦆R ρ rs   = ⦅ t ⦆R ρ       rs (⦅ u ⦆R ρ rs)
⦅ gen t     ⦆R ρ rs R = ⦅ t ⦆R (R , ρ) rs
⦅ inst t B  ⦆R ρ rs   = ⦅ t ⦆R ρ       rs (⟦ B ⟧R ρ)
⦅ conv s t  ⦆R ρ      = ⦅ s ⦆SR ρ ∘ ⦅ t ⦆R ρ
⦅ convG t w ⦆R ρ      = ⦅ t ⦆R ρ ∘ ⦅ w ⦆GWR ρ
⦅ wk t      ⦆R ρ      = ⦅ t ⦆R ρ ∘ proj₂
⦅ wkTy t    ⦆R        = ⦅ t ⦆R ∘ proj₂


-- Identity extension
---------------------------------------------------------------------------

-- Environment of Identity relations

IdR : ∀ Δ (ξ : ⟪ Δ ⟫) → ⟪ Δ ⟫R ξ ξ
IdR []      ξ       = _
IdR (k ∷ Δ) (S , ξ) = _≡_ , IdR Δ ξ

-- I do not see how to prove the identity extension lemma (IEL):
-- It is not clear how to show that ⟦∀X.A⟧R is reflexive.
-- This would work in homogeneous parametricity.

mutual

  idExt : (A : Ty Δ l) {ξ : ⟪ Δ ⟫} → ∀{a} → ⟦ A ⟧R (IdR _ ξ) a a
  idExt var = refl
  idExt (A ⇒ B) r rewrite idExt⁻ A r = idExt B
  idExt (∀̇ A) R = {!!}  -- DOES NOT SEEM TO HOLD because heterogeneous!?
  idExt (A [ τ ]) = {!idExt A!}

  idExt⁻ : (A : Ty Δ l) {ξ : ⟪ Δ ⟫} → ∀{a a'} → ⟦ A ⟧R (IdR _ ξ) a a' → a ≡ a'
  idExt⁻ var = id

  idExt⁻ (A ⇒ B) F = funExt λ a → idExt⁻ B (F (idExt A))
    where postulate
      funExt : Extensionality _ _

  idExt⁻ (∀̇ A) F = funExt λ S → idExt⁻ A (F _≡_)
    where postulate
      funExt : Extensionality _ _

  idExt⁻ (A [ τ ]) = {!!}


---------------------------------------------------------------------------
-- Theorems for free!
---------------------------------------------------------------------------

-- Theorem 1:
-- ⊢ t : ∀ X. X → X  is the identity
---------------------------------------------------------------------------

⊤₀ = ⊤ {ℓ = lzero}
l1 = lsuc lzero

TId : Ty [] l1
TId = ∀̇ (var ⇒ var)

module Identity (S : Set) (s : S) (t : Tm [] TId) where

  -- Unary parametricity is enough

  R : REL S ⊤₀ lzero
  R s₁ s₂ = s₁ ≡ s

  f : ⟦ TId ⟧ _
  f = ⦅ t ⦆ _ _

  ⦅t⦆ : ⟦ TId ⟧R _ f f
  ⦅t⦆ = ⦅ t ⦆R _ _

  thm : f S s ≡ s
  thm = ⦅t⦆ R refl
  -- thm = ⦅t⦆ R {a = s} {a' = _} refl

id-thm : (t : Tm [] TId) → ∀ S (s : S) → ⦅ t ⦆ _ _ S s ≡ s
id-thm t S s = Identity.thm S s t

-- Theorem 2:
-- ⊢ t : ∀ X. (X → X) → (X → X)  is a Church numeral
---------------------------------------------------------------------------

TNat : Ty [] l1
TNat = ∀̇ ((var ⇒ var) ⇒ (var ⇒ var))

module Numeral (X : Set) (s : X → X) (z : X) (t : Tm [] TNat) where

  -- Unary parametricity is enough

  R : REL X ⊤₀ lzero
  R x _ = ∃ λ n → x ≡ fold z s n

  ⦅z⦆ : R z _
  ⦅z⦆ = 0 , refl

  ⦅s⦆ : ∀{x₁ x₂} → R x₁ x₂ → R (s x₁) _
  ⦅s⦆ (n , refl) = suc n , refl

  thm : ∃ λ n → ⦅ t ⦆ _ _ X s z ≡ fold z s n
  thm = ⦅ t ⦆R _ _ R ⦅s⦆ ⦅z⦆

-- Theorem 3: Parametricity is anti-classical.
-- ¬ (⊢ t : ∀ A B. ((A → B) → A) → A)
---------------------------------------------------------------------------

module Peirce where

  P : Ty (lzero ∷ lzero ∷ []) lzero
  P = let A = var; B = Wk var in
      ((A ⇒ B) ⇒ A) ⇒ A

  -- Unary parametricity is sufficient.
  -- We instantiate A = ⊤, RA = ⊥ and B = ⊥.  RB is arbitrary.

  thm : (t : Tm [] P) → ⊥
  thm t =
    let
      A  = ⊤₀                -- must be inhabited
      B  = ⊥                 -- must be empty
      ξ  = A , B , _
      ⦅t⦆ = ⦅ t ⦆ ξ _

      RA : REL A ⊤₀ lzero
      RA _ _ = ⊥             -- must be empty

      RB : REL B ⊤₀ lzero
      RB _ _ = ⊤             -- Does not matter

      ρ = RA , RB , _
    in
      ⦅ t ⦆R ρ _ λ {f : A → B} _ → f _

-- Theorem 4:
-- A ≅ ∀ X. (A → X) → X
---------------------------------------------------------------------------

-- to : A → ∀ X. (A → X) → X
-- to a = ΛX. λ(k : A → X). k a
--
-- from : (∀ X. (A → X) → X) → A
-- from t = t A id
--
-- from (to a) = a  trivial by computation
-- to (from t) = t  difficult direction, by parametricity
--
-- Let t' = to (from t).  We show
--
--   ⦅t'⦆ ⟦∀X. (A → X) → X⟧R ⦅t⦆
--
-- by parametricity on t.

module Wrap
    -- Assume an arbitrary type A
    (A : Ty [] lzero)

    -- Let ¬¬A = (A → X) → X
    (let ¬¬A : Ty (lzero ∷ []) lzero
         ¬¬A = (Wk A ⇒ var) ⇒ var)

    -- Let A' = ∀ X. (A → X) → X
    (let A' : Ty [] l1
         A' = ∀̇ ¬¬A)

    -- Assume an arbitrary term t of type A'
    (t : Tm [] A')
  where

  -- t₀ = from t
  -- t₀ = t A id
  --
  t₀ : Tm [] A
  t₀ = app (conv s (inst t A)) (abs (var here))
    where
    -- Boilerplate: Propagating the instantiation
    s : ((Wk A ⇒ var) ⇒ var) [ sgS A ]  →s  (A ⇒ A) ⇒ A
    s = step arrS (arr (step arrS (arr (step compS (step idS (step idS refl)))
                                                   (step prjS refl)))
                       (step prjS refl))

  -- t' = to t₀
  -- t' = ΛX λ(k : A ⇒ X). k t₀
  --
  t' : Tm [] A'
  t' = gen (abs (app (var here) (wk (wkTy t₀))))

  ⟦A⟧  = ⟦ A ⟧ _
  ⦅t⦆  = ⦅ t ⦆ _ _
  ⦅t'⦆ = ⦅ t' ⦆ _ _

  -- Goal: show that ⦅t'⦆ is extensionally equal to ⦅t⦆
  -- We are using ⟦A⟧R as extensional notion of equality on ⟦A⟧.

  thm : ⟦ A' ⟧R _ ⦅t'⦆ ⦅t⦆
  thm {S} {S'} R {k} {k'} ⟦k⟧ = ⦅ t ⦆R _ _ R' ⟦k⟧
    -- Goal:  k (⦅t⦆ ⟦A⟧ id)  `R`  ⦅t⦆ S' k'
    -- ⟦k⟧ :  ⟦A⟧R a a' → R (k a) (k' a')
    where
    R' : REL ⟦A⟧ S' lzero
    R' a b = R (k a) b


---------------------------------------------------------------------------
-- TRASH
---------------------------------------------------------------------------

  -- module _ (E⟦B⟧ : Setoid lzero lzero) where

  --   ⟦B⟧ = E⟦B⟧ .Carrier
  --   -- Goal: show that ⦅t'⦆ is extensionally equal to ⦅t⦆
  --   thm :  E⟦ ¬¬A ⟧ (E⟦B⟧ , _) ._≈_ (⦅t'⦆ {!⟦B⟧!} {!!}) {!!}  -- ⦅t'⦆ ⦅t⦆
  --   thm = {!!}


{-

-- Proof from
-- Abel, Bernardy, ICFP 2020, Section 8.1

  f = ⦅ t ⦆ _ _

  a₀ = ⦅ t₀ ⦆ _ _
  ⦅t₀⦆ = ⦅ t₀ ⦆ _ _

  ⟦t₀⟧ : ⟦ A ⟧R _ ⦅t₀⦆ ⦅t₀⦆
  ⟦t₀⟧ = ⦅ t₀ ⦆R _ _

  module _
      -- (B : Ty [] lzero)
      -- (let ⟦B⟧ = ⟦ B ⟧ _)
      (⟦B⟧ : Set)
      (k : ⟦A⟧ → ⟦B⟧)
      -- Without the identity extension lemma, k needs to be a morphism
    where

    R : REL ⟦A⟧ ⟦B⟧ lzero
    R a b = k a ≡ b

    lem : ∀{a a'} → ⟦ A ⟧R _ a a' → R a (k a')
    lem r = {!!}

    -- R : REL ⟦A⟧ ⟦B⟧ lzero
    -- R a b = ∀{a'} → ⟦ A ⟧R _ a a' → k a' ≡ b

    -- lem : ∀{a a'} → ⟦ A ⟧R _ a a' → R a (k a')
    -- lem r r' = {!!}

    goal : k (⦅t⦆ ⟦A⟧ id) ≡ ⦅t⦆ ⟦B⟧ k
    goal = ⦅ t ⦆R _ _ R {!!} -- ⟦t₀⟧

  -- Goal: show that ⦅t'⦆ is extensionally equal to ⦅t⦆
  thm : ∀ S (k : ⟦A⟧ → S) → ⦅t'⦆ S k ≡ ⦅t⦆ S k
  -- thm : ⟦ A' ⟧R _ ⦅t'⦆ ⦅t⦆  -- ⦅ t' ⦆ _ _ ≡ ⦅ t ⦆ _ _
  thm S k = goal S k

-- More exercises:
--
--  A × B ≅ ∀ X. (A → B → X) → X
--  A + B ≅ ∀ X. (A → X) → (B → X) → X

-- Parametricity for bounded polymorphism:
--
-- ⟦∀X≤A.B⟧R ξ ξ' ρ h h'
--   = (S S' : Set) (f : S → ⟦A⟧ ξ) (f' : S' → ⟦A⟧ ξ')
--     (R : REL S S') (g : ∀ s s' → R s s' → ⟦A⟧R ξ ξ' ρ (f s) (f' s'))
--     → ⟦B⟧R (S,ξ) (S',ξ') ((R,g),ρ) (h S) (h' S')

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
