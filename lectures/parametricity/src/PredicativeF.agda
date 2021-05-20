open import Level renaming (zero to lzero; suc to lsuc)

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤)

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
  var : Ty (k ∷ []) k
  wk  : (A : Ty Δ l) → Ty (k ∷ Δ) l
  _⇒_ : (A : Ty Δ k) (B : Ty Δ l) → Ty Δ (k ⊔ l)
  ∀̇   : (A : Ty (k ∷ Δ) l) → Ty Δ (lsuc k ⊔ l)

variable
  A A' B B' : Ty Δ k

-- Standard model for types: sets
---------------------------------

-- The level of a context

⟨_⟩ : KCxt → Level
⟨ [] ⟩     = lzero
⟨ l ∷ ls ⟩ = l ⊔ ⟨ ls ⟩

-- Type environments  ρ : ⟪ Δ ⟫

⟪_⟫ : (Δ : KCxt) → Set (lsuc ⟨ Δ ⟩)
⟪ []     ⟫ = ⊤
⟪ l ∷ ls ⟫ = Set l × ⟪ ls ⟫

-- -- Looking up in type environment ρ

-- ⟦_⟧X : (X : k ∈ Δ) → ⟪ Δ ⟫ → Set k
-- ⟦ here!   ⟧X (A , ρ) = A
-- ⟦ there X ⟧X (A , ρ) = ⟦ X ⟧X ρ

-- Type interpretation

⟦_⟧ : (A : Ty Δ k) → ⟪ Δ ⟫ → Set k
⟦ var   ⟧ (S , _) = S
⟦ wk A  ⟧ (_ , ρ) = ⟦ A ⟧ ρ
⟦ A ⇒ B ⟧ ρ       = ⟦ A ⟧ ρ → ⟦ B ⟧ ρ
⟦ ∀̇ A   ⟧ ρ       = (S : Set _) → ⟦ A ⟧ (S , ρ)

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
⟦ []    ⟧G ρ       = ⊤
⟦ A ∷ Γ ⟧G ρ       = ⟦ A ⟧ ρ × ⟦ Γ ⟧G ρ
⟦ wk Γ  ⟧G (_ , ρ) =  ⟦ Γ ⟧G ρ

-- Looking up the value of a variable in an environment

⦅_⦆x : {Γ : Cxt Δ} (x : A ∈G Γ) (ρ : ⟪ Δ ⟫) (η : ⟦ Γ ⟧G ρ) → ⟦ A ⟧ ρ
⦅ here    ⦆x ρ (a , η) = a
⦅ there x ⦆x ρ (a , η) = ⦅ x ⦆x ρ η
⦅ wk x    ⦆x (_ , ρ) η = ⦅ x ⦆x ρ η

-- Terms
--------

-- need context weakening and type substitution

data Tm {Δ : KCxt} (Γ : Cxt Δ) : ∀{k} → Ty Δ k → Set where
  var  : (x : A ∈G Γ) → Tm Γ A
  abs  : (t : Tm (A ∷ Γ) B) → Tm Γ (A ⇒ B)
  app  : (t : Tm Γ (A ⇒ B)) (u : Tm Γ A) → Tm Γ B
  gen  : (t : Tm (wk Γ) A) → Tm Γ (∀̇ A)
  -- inst : (t : Tm Γ (∀̇ {k = k} A)) (B : Ty Δ k) → Tm Γ {!!}

⦅_⦆ : {Γ : Cxt Δ} (t : Tm Γ A) (ρ : ⟪ Δ ⟫) (η : ⟦ Γ ⟧G ρ) → ⟦ A ⟧ ρ
⦅ var x ⦆ ρ η   = ⦅ x ⦆x ρ η
⦅ abs t ⦆ ρ η a = ⦅ t ⦆ ρ (a , η)
⦅ app t u ⦆ ρ η = ⦅ t ⦆ ρ η (⦅ u ⦆ ρ η)
⦅ gen t ⦆ ρ η S = ⦅ t ⦆ (S , ρ) η

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
