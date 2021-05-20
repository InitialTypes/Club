open import Level renaming (zero to lzero; suc to lsuc)

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤)


import Relation.Binary as R; open R using (REL)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

pattern here! = here refl

-- Kinding contexts
-------------------

KCxt = List Level

variable
  k l : Level
  m n : ℕ
  Δ Δ' : KCxt

-- Types
--------

data Ty : (Δ : KCxt) (k : Level) → Set where
  var  : Ty (k ∷ []) k
  wk   : (A : Ty Δ l) → Ty (k ∷ Δ) l
  _⇒_  : (A : Ty Δ k) (B : Ty Δ l) → Ty Δ (k ⊔ l)
  ∀̇    : (A : Ty (k ∷ Δ) l) → Ty Δ (lsuc k ⊔ l)
  _[_] : (A : Ty (k ∷ Δ) l) (B : Ty Δ k) → Ty Δ l

variable
  A A' B B' : Ty Δ k

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

-- -- Looking up in type environment ξ

-- ⟦_⟧X : (X : k ∈ Δ) → ⟪ Δ ⟫ → Set k
-- ⟦ here!   ⟧X (A , ξ) = A
-- ⟦ there X ⟧X (A , ξ) = ⟦ X ⟧X ξ

-- Type interpretation

⟦_⟧ : (A : Ty Δ k) → ⟪ Δ ⟫ → Set k
⟦ var   ⟧ (S , _) = S
⟦ wk A  ⟧ (_ , ξ) = ⟦ A ⟧ ξ
⟦ A ⇒ B ⟧ ξ       = ⟦ A ⟧ ξ → ⟦ B ⟧ ξ
⟦ ∀̇ A   ⟧ ξ       = (S : Set _) → ⟦ A ⟧ (S , ξ)
⟦ A [ B ] ⟧ ξ     = ⟦ A ⟧ (⟦ B ⟧ ξ , ξ)

-- Typing contexts
------------------

-- TY : KCxt → Set
-- TY Δ = ∃ (Ty Δ)

data Cxt : (Δ : KCxt) → Set where
  [] : Cxt Δ
  _∷_ : (A : Ty Δ k) (Γ : Cxt Δ) → Cxt Δ
  wk  : (Γ : Cxt Δ) → Cxt (k ∷ Δ)

variable
  Γ Γ' : Cxt Δ

data _∈G_ : (A : Ty Δ k) (Γ : Cxt Δ) → Set where
  here  : A ∈G (A ∷ Γ)
  there : (x : A ∈G Γ) → A ∈G (B ∷ Γ)
  wk    : (x : A ∈G Γ) → wk {k = k} A ∈G wk Γ

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
⦅ here    ⦆x ξ (a , η) = a
⦅ there x ⦆x ξ (a , η) = ⦅ x ⦆x ξ η
⦅ wk x    ⦆x (_ , ξ) η = ⦅ x ⦆x ξ η

-- Terms
--------

-- need context weakening and type substitution

data Tm {Δ : KCxt} (Γ : Cxt Δ) : ∀{k} → Ty Δ k → Set where
  var  : (x : A ∈G Γ)                          → Tm Γ A
  abs  : (t : Tm (A ∷ Γ) B)                    → Tm Γ (A ⇒ B)
  app  : (t : Tm Γ (A ⇒ B)) (u : Tm Γ A)       → Tm Γ B
  gen  : (t : Tm (wk Γ) A)                     → Tm Γ (∀̇ A)
  inst : (t : Tm Γ (∀̇ {k = k} A)) (B : Ty Δ k) → Tm Γ (A [ B ])

-- Standard model of terms (functions)

⦅_⦆ : {Γ : Cxt Δ} (t : Tm Γ A) (ξ : ⟪ Δ ⟫) (η : ⟦ Γ ⟧G ξ) → ⟦ A ⟧ ξ
⦅ var x    ⦆ ξ η   = ⦅ x ⦆x ξ η
⦅ abs t    ⦆ ξ η a = ⦅ t ⦆ ξ (a , η)
⦅ app t u  ⦆ ξ η   = ⦅ t ⦆ ξ η (⦅ u ⦆ ξ η)
⦅ gen t    ⦆ ξ η S = ⦅ t ⦆ (S , ξ) η
⦅ inst t B ⦆ ξ η   = ⦅ t ⦆ ξ η (⟦ B ⟧ ξ)

-- Relational model in sets
---------------------------

⟪_⟫R : (Δ : KCxt) (ξ ξ' : ⟪ Δ ⟫) → Set (lsuc ⟨ Δ ⟩)
⟪ []    ⟫R _       _         = ⊤
⟪ k ∷ Δ ⟫R (S , ξ) (S' , ξ') = REL S S' k × ⟪ Δ ⟫R ξ ξ'

-- Relational interpretation of types

⟦_⟧R : (A : Ty Δ k) (ξ ξ' : ⟪ Δ ⟫) (ρ : ⟪ Δ ⟫R ξ ξ') → REL (⟦ A ⟧ ξ) (⟦ A ⟧ ξ') k

⟦ var     ⟧R (S , _) (S' , _) (R , _) = R
⟦ wk A    ⟧R (_ , ξ) (_ , ξ') (_ , ρ) = ⟦ A ⟧R ξ ξ' ρ

⟦ A ⇒ B   ⟧R ξ ξ' ρ f f' = ∀ a a'
                         → ⟦ A ⟧R ξ ξ' ρ a a'
                         → ⟦ B ⟧R ξ ξ' ρ (f a) (f' a')

⟦ ∀̇ A     ⟧R ξ ξ' ρ f f' = ∀ S S' (R : REL S S' _)
                         → ⟦ A ⟧R (S , ξ) (S' , ξ') (R , ρ) (f S) (f' S')

⟦ A [ B ] ⟧R ξ ξ' ρ =  ⟦ A ⟧R (⟦ B ⟧ ξ , ξ) (⟦ B ⟧ ξ' , ξ') (⟦ B ⟧R ξ ξ' ρ , ρ)

-- Relational interpretation of contexts

⟦_⟧GR : (Γ : Cxt Δ) (ξ ξ' : ⟪ Δ ⟫) (ρ : ⟪ Δ ⟫R ξ ξ') → REL (⟦ Γ ⟧G ξ) (⟦ Γ ⟧G ξ') ⟨ Γ ⟩G
⟦ []    ⟧GR ξ ξ' ρ _ _               = ⊤
⟦ A ∷ Γ ⟧GR ξ ξ' ρ (a , η) (a' , η') = ⟦ A ⟧R ξ ξ' ρ a a'  ×  ⟦ Γ ⟧GR ξ ξ' ρ η η'
⟦ wk Γ  ⟧GR (_ , ξ) (_ , ξ') (_ , ρ) = ⟦ Γ ⟧GR ξ ξ' ρ


-- Fundamental theorem of logical relations

⦅_⦆xR : {Γ : Cxt Δ} (x : A ∈G Γ)
      (ξ ξ' : ⟪ Δ ⟫) (ρ : ⟪ Δ ⟫R ξ ξ')
      (η : ⟦ Γ ⟧G ξ) (η' : ⟦ Γ ⟧G ξ') (rs : ⟦ Γ ⟧GR ξ ξ' ρ η η')
      → ⟦ A ⟧R ξ ξ' ρ (⦅ x ⦆x ξ η) (⦅ x ⦆x ξ' η')
⦅ here    ⦆xR ξ ξ' ρ (a , _) (a' , _) (r , _) = r
⦅ there x ⦆xR ξ ξ' ρ (_ , η) (_ , η') (_ , rs) = ⦅ x ⦆xR ξ ξ' ρ η η' rs
⦅ wk x    ⦆xR (_ , ξ) (_ , ξ') (_ , ρ) η η' rs = ⦅ x ⦆xR ξ ξ' ρ η η' rs

⦅_⦆R : {Γ : Cxt Δ} (t : Tm Γ A)
      {ξ ξ' : ⟪ Δ ⟫} (ρ : ⟪ Δ ⟫R ξ ξ')
      {η : ⟦ Γ ⟧G ξ} {η' : ⟦ Γ ⟧G ξ'} (rs : ⟦ Γ ⟧GR ξ ξ' ρ η η')
      → ⟦ A ⟧R ξ ξ' ρ (⦅ t ⦆ ξ η) (⦅ t ⦆ ξ' η')
⦅ var x    ⦆R ρ rs = {!!}
⦅ abs t    ⦆R ρ rs = {!!}
⦅ app t u  ⦆R ρ rs = {!!}
⦅ gen t    ⦆R ρ rs = {!!}
⦅ inst t B ⦆R ρ rs = {!!}

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
