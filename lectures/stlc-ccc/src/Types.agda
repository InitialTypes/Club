-- Simple types

data Ty : Set where
  𝟙    : Ty                -- \b1
  _⇒_ : (a b : Ty) → Ty   -- \r2
  _*_ :  (a b : Ty) → Ty

-- Typing contexts

data Cxt : Set where
  ε   : Cxt
  _,_ : (Γ : Cxt) (a : Ty) → Cxt

infix 19 _∈_

data _∈_ (a : Ty) : (Γ : Cxt) → Set where
  𝟘   : {Γ : Cxt} → a ∈ Γ , a
  𝟙+_ : {Γ : Cxt} {b : Ty} → a ∈ Γ → a ∈ Γ , b
