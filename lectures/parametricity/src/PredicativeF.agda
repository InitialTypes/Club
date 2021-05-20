-- Parametricity for predicative System F
---------------------------------------------------------------------------

open import Level renaming (zero to lzero; suc to lsuc)

open import Data.List.Base                        using (List; []; _∷_)
open import Data.List.Relation.Unary.Any          using (Any; here; there)
open import Data.List.Membership.Propositional    using (_∈_)

open import Data.Nat.Base                         using (ℕ; zero; suc)
open import Data.Nat.GeneralisedArithmetic        using (fold)

open import Data.Product                          using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic                 using (⊤)

open import Relation.Binary                       using (REL)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

pattern here! = here refl

-- System F extends the simply typed lambda calculus by parametric
-- polymorphism.  The new type former is `∀X.A` which binds type
-- variable `X` in type `A`.  A polymorphic term `t : ∀X.A` can be
-- instantiated to any type `B`, yielding `t B : A[X=B]`.

-- reverse         : forall a . [a] → [a]
-- reverse-natural : reverse . map f = map f . reverse

-- Literature:

-- John C. Reynolds:
-- Types, Abstraction and Parametric Polymorphism.
-- IFIP Congress 1983: 513-523

-- Wadler, Theorems for free



-- Kinding contexts
-------------------

KCxt = List Level

variable
  k l : Level
  Δ Δ' : KCxt

-- Types
--------

-- A,B ::= X | A → B | ∀(X : ★ₙ). A

-- Δ = ... X:★ₙ ...
-- Δ ⊢ A : ★ₙ
-- A : (Δ ⊢ ★ₙ)

--   Δ, X : ★ₖ ⊢ A : ★ₗ
--   ------------------------------
--   Δ ⊢ ∀ (X:★ₖ).A : ★(max(k+1,l))

data Ty : (Δ : KCxt) (k : Level) → Set where
  var  :                                   Ty (k ∷ []) k
  wk   : (A : Ty Δ l)                    → Ty (k ∷ Δ) l

  _⇒_  : (A : Ty Δ k) (B : Ty Δ l)       → Ty Δ (k ⊔ l)
  ∀̇    : (A : Ty (k ∷ Δ) l)              → Ty Δ (lsuc k ⊔ l)
  _[_] : (A : Ty (k ∷ Δ) l) (B : Ty Δ k) → Ty Δ l

variable
  A A' B B' : Ty Δ k
  S S'      : Set k

-- Standard model for types: sets
---------------------------------

-- The level of a context

⟨_⟩ : KCxt → Level
⟨ [] ⟩     = lzero
⟨ l ∷ ls ⟩ = l ⊔ ⟨ ls ⟩

-- Type environments  ξ : ⟪ Δ ⟫

⟪_⟫ : (Δ : KCxt) → Set (lsuc ⟨ Δ ⟩)
⟪ []     ⟫ = ⊤
⟪ l ∷ ls ⟫ = Set l × ⟪ ls ⟫

-- Type interpretation

⟦_⟧ : (A : Ty Δ k) (ξ : ⟪ Δ ⟫) → Set k
⟦ var   ⟧ (S , _) = S
⟦ wk A  ⟧ (_ , ξ) = ⟦ A ⟧ ξ
⟦ A ⇒ B ⟧ ξ       = ⟦ A ⟧ ξ → ⟦ B ⟧ ξ
⟦ ∀̇ A   ⟧ ξ       = ∀ S → ⟦ A ⟧ (S , ξ)
⟦ A [ B ] ⟧ ξ     = ⟦ A ⟧ (⟦ B ⟧ ξ , ξ)

-- Typing contexts
------------------

-- Δ;Γ ⊢ t : A   where Δ ⊢ A : ★ₙ and Δ ⊢ Γ

data Cxt : (Δ : KCxt) → Set where
  []  : Cxt Δ
  _∷_ : (A : Ty Δ k) (Γ : Cxt Δ) → Cxt Δ
  wk  : (Γ : Cxt Δ) → Cxt (k ∷ Δ)

variable
  Γ Γ' : Cxt Δ

data _∈G_ : (A : Ty Δ k) (Γ : Cxt Δ) → Set where
  here  : A ∈G (A ∷ Γ)
  there : (x : A ∈G Γ) → A ∈G (B ∷ Γ)
  wk    : (x : A ∈G Γ) → wk {k = k} A ∈G wk Γ

-- Standard interpretation of typing context

⟨_⟩G : (Γ : Cxt Δ) → Level
⟨ []              ⟩G = lzero
⟨ _∷_ {k = k} A Γ ⟩G = k ⊔ ⟨ Γ ⟩G
⟨ wk Γ            ⟩G = ⟨ Γ ⟩G

-- Environments

⟦_⟧G : (Γ : Cxt Δ) → ⟪ Δ ⟫ → Set ⟨ Γ ⟩G
⟦ []    ⟧G ξ       = ⊤
⟦ A ∷ Γ ⟧G ξ       = ⟦ A ⟧ ξ × ⟦ Γ ⟧G ξ
⟦ wk Γ  ⟧G (_ , ξ) = ⟦ Γ ⟧G ξ

-- Looking up the value of a variable in an environment

⦅_⦆x : {Γ : Cxt Δ} (x : A ∈G Γ) (ξ : ⟪ Δ ⟫) (η : ⟦ Γ ⟧G ξ) → ⟦ A ⟧ ξ
⦅ here    ⦆x ξ (a , _) = a
⦅ there x ⦆x ξ (_ , η) = ⦅ x ⦆x ξ η
⦅ wk x    ⦆x (_ , ξ) η = ⦅ x ⦆x ξ η

-- Terms
--------

-- need context weakening and type substitution

data Tm {Δ : KCxt} (Γ : Cxt Δ) : ∀{k} → Ty Δ k → Set where

  var  : (x : A ∈G Γ)                          → Tm Γ A
  abs  : (t : Tm (A ∷ Γ) B)                    → Tm Γ (A ⇒ B)
  app  : (t : Tm Γ (A ⇒ B)) (u : Tm Γ A)       → Tm Γ B

  -- Generalization:
  -- ΛX:★ₙ.t : ∀X:★ₙ.A  when t : A
  -- Δ; Γ ⊢ ΛX:★ₙ.t : ∀X:★ₙ.A   when Δ,X:★ₙ; Γ ⊢ t : A  and X ∉ FV(Γ)

  gen  : (t : Tm (wk Γ) A)                     → Tm Γ (∀̇ A)

  -- Instantiation:
  -- t B : A[B/X]  when  t : ∀X:★ₙ.A  and B : ★ₙ

  inst : (t : Tm Γ (∀̇ {k = k} A)) (B : Ty Δ k) → Tm Γ (A [ B ])

-- Standard model of terms (functions)

⦅_⦆ : {Γ : Cxt Δ} (t : Tm Γ A) (ξ : ⟪ Δ ⟫) (η : ⟦ Γ ⟧G ξ) → ⟦ A ⟧ ξ
⦅ var x    ⦆ ξ η   = ⦅ x ⦆x ξ       η
⦅ abs t    ⦆ ξ η a = ⦅ t ⦆  ξ (a , η)
⦅ app t u  ⦆ ξ η   = ⦅ t ⦆  ξ       η (⦅ u ⦆ ξ η)
⦅ gen t    ⦆ ξ η S = ⦅ t ⦆  (S , ξ) η
⦅ inst t B ⦆ ξ η   = ⦅ t ⦆  ξ       η (⟦ B ⟧ ξ)

-- Relational model in sets
---------------------------

⟪_⟫R : (Δ : KCxt) (ξ ξ' : ⟪ Δ ⟫) → Set (lsuc ⟨ Δ ⟩)
⟪ []    ⟫R _       _         = ⊤
⟪ k ∷ Δ ⟫R (S , ξ) (S' , ξ') = REL S S' k × ⟪ Δ ⟫R ξ ξ'

-- Relational interpretation of types

-- REL S T k = S → T → Set k

⟦_⟧R : (A : Ty Δ k) {ξ ξ' : ⟪ Δ ⟫} (ρ : ⟪ Δ ⟫R ξ ξ') → REL (⟦ A ⟧ ξ) (⟦ A ⟧ ξ') k

⟦ var     ⟧R (R , _) = R
⟦ wk A    ⟧R (_ , ρ) = ⟦ A ⟧R ρ

⟦ A ⇒ B   ⟧R ρ f f'  = ∀ {a a'}
                     → ⟦ A ⟧R ρ a a'
                     → ⟦ B ⟧R ρ (f a) (f' a')

-- ⟦★ₖ⟧ S S' = REL S S' k

⟦ ∀̇ A     ⟧R ρ f f'  = ∀ {S S'} (R : REL S S' _)
                     → ⟦ A ⟧R (R , ρ) (f S) (f' S')

⟦ A [ B ] ⟧R ρ       = ⟦ A ⟧R (⟦ B ⟧R ρ , ρ)

-- Relational interpretation of contexts

⟦_⟧GR : (Γ : Cxt Δ) {ξ ξ' : ⟪ Δ ⟫} (ρ : ⟪ Δ ⟫R ξ ξ') → REL (⟦ Γ ⟧G ξ) (⟦ Γ ⟧G ξ') ⟨ Γ ⟩G
⟦ []    ⟧GR ρ _ _               = ⊤
⟦ A ∷ Γ ⟧GR ρ (a , η) (a' , η') = ⟦ A ⟧R ρ a a'  ×  ⟦ Γ ⟧GR ρ η η'
⟦ wk Γ  ⟧GR (_ , ρ)             = ⟦ Γ ⟧GR ρ


-- Fundamental theorem of logical relations for variables

⦅_⦆xR : {Γ : Cxt Δ} {A : Ty Δ k}       (x : A ∈G Γ)
       {ξ : ⟪ Δ ⟫  } {ξ' : ⟪ Δ ⟫   }  (ρ  : ⟪ Δ ⟫R ξ ξ')
       {η : ⟦ Γ ⟧G ξ} {η' : ⟦ Γ ⟧G ξ'} (rs : ⟦ Γ ⟧GR ρ η η')

     → ⟦ A ⟧R ρ (⦅ x ⦆x ξ η) (⦅ x ⦆x ξ' η')

⦅ here    ⦆xR ρ  (r , _)  = r
⦅ there x ⦆xR ρ  (_ , rs) = ⦅ x ⦆xR ρ rs
⦅ wk x    ⦆xR (_ , ρ) rs  = ⦅ x ⦆xR ρ rs

-- Fundamental theorem of logical relations

⦅_⦆R : {Γ : Cxt Δ}    {A : Ty Δ k}      (t : Tm Γ A)
       {ξ : ⟪ Δ ⟫  }  {ξ' : ⟪ Δ ⟫   }   (ρ  : ⟪ Δ ⟫R ξ ξ')
       {η : ⟦ Γ ⟧G ξ} {η' : ⟦ Γ ⟧G ξ'}  (rs : ⟦ Γ ⟧GR ρ η η')

    → ⟦ A ⟧R ρ (⦅ t ⦆ ξ η) (⦅ t ⦆ ξ' η')

⦅ var x    ⦆R ρ rs   = ⦅ x ⦆xR ρ      rs
⦅ abs t    ⦆R ρ rs r = ⦅ t ⦆R ρ (r , rs)
⦅ app t u  ⦆R ρ rs   = ⦅ t ⦆R ρ       rs (⦅ u ⦆R ρ rs)
⦅ gen t    ⦆R ρ rs R = ⦅ t ⦆R (R , ρ) rs
⦅ inst t B ⦆R ρ rs   = ⦅ t ⦆R ρ       rs (⟦ B ⟧R ρ)


-- Theorems for free!

-- Application 1:
-- ⊢ t : ∀ X. X → X  is the identity

l1 = lsuc lzero

TId : Ty [] l1
TId = ∀̇ (var ⇒ var)

module Identity (S : Set) (s : S) (t : Tm [] TId) where

  -- Unary parametricity is enough

  R : REL S (⊤ {ℓ = lzero}) lzero
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

-- Application 2:
-- ⊢ t : ∀ X. (X → X) → (X → X)  is a Church numeral

TNat : Ty [] l1
TNat = ∀̇ ((var ⇒ var) ⇒ (var ⇒ var))

module Numeral (X : Set) (s : X → X) (z : X) (t : Tm [] TNat) where

  -- Unary parametricity is enough

  R : REL X (⊤ {ℓ = lzero}) lzero
  R x₁ x₂ = ∃ λ n → x₁ ≡ fold z s n

  ⦅z⦆ : R z _
  ⦅z⦆ = 0 , refl

  ⦅s⦆ : ∀{x₁ x₂} → R x₁ x₂ → R (s x₁) _
  ⦅s⦆ (n , refl) = suc n , refl

  thm : ∃ λ n → ⦅ t ⦆ _ _ X s z ≡ fold z s n
  thm = ⦅ t ⦆R _ _ R ⦅s⦆ ⦅z⦆
  -- thm = ⦅ t ⦆R _ _ R {a' = s} (⦅s⦆ {x₂ = z}) {a' = z} ⦅z⦆




-- Needs impredicativity:
--
-- -- Application  A ≅ ∀ X. (A → X) → X
-- -- x : A                ⊢ ΛX k. k x : ∀ X. (A → X) → X
-- -- y : ∀ X. (A → X) → X ⊢ y A id : A

-- y ≡ ΛX k. k (y A id)

-- module Wrap (A : Ty [] l1) (let A' : Ty [] l1; A' = ∀̇ ((wk A ⇒ var) ⇒ var)) (t : Tm [] A') where

--   -- -- A' = ∀ X. (A → X) → X
--   -- A' : Ty [] l1
--   -- A' = ∀̇ ((wk A ⇒ var) ⇒ var)

--   -- module _ (t : Tm [] A') where

--   -- t' = ΛX λ(k : A ⇒ X). k (t A (λ(x:A).x))
--   t' : Tm [] A'
--   t' = gen (abs (app (var here) (app {!inst t A!} (abs (var here)))))

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
