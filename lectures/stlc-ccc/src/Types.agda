-- Simple types

data Ty : Set where
  𝟙    : Ty                -- \b1
  _⇒_ : (a b : Ty) → Ty   -- \r2
  _*_ :  (a b : Ty) → Ty

-- Typing contexts

data Cxt : Set where
  ε   : Cxt
  _,_ : (Γ : Cxt) (a : Ty) → Cxt
