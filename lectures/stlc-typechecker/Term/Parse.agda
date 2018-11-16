
module Term.Parse where

open import Prelude
import Text.Parse as P

open import Term.Lex
open import Type
open import Term
open P Token

private
  pi : P String
  pi = symbol >>= λ
        { (ti x) → return x
        ; _      → fail }

  pn : P Nat
  pn = symbol >>= λ
         { (tn n) → return n
         ; _ → fail }

  pi! : String → P ⊤
  pi! s = token (ti s)

  p[ = token t[
  p] = token t]
  p: = token t:
  p= = token t=
  pλ = token tλ
  p→ = token t→

  paren : ∀ {A} → P A → P A
  paren p = p[ *> p <* p]

  {-# NON_TERMINATING #-}
  pType pType₁ : P Type

  pType  = pType₁ +++ _=>_ <$> pType₁ <* p→ <*> pType
  pType₁ = nat <$ pi! "nat" +++ paren pType

  apps : RawTerm → List RawTerm → RawTerm
  apps f xs = foldl app f xs

  mkLet : Name → List (Name × Type) → Type → RawTerm → RawTerm → RawTerm
  mkLet f args a e₁ e₂ =
    app (lam f (foldr (_=>_ ∘ snd) a args) e₂) (foldr (uncurry lam) e₁ args)

  mkVar : String → RawTerm
  mkVar "suc" = suc
  mkVar x = var x

  {-# NON_TERMINATING #-}
  pLam pApp pAtom : P RawTerm
  pArg : P (Name × Type)

  pLam =
    pApp
    +++ uncurry lam <$ pλ <*> pArg
            <*  p→ <*> pLam
    +++ mkLet <$ pi! "let" <*> pi <*> many pArg <* p: <*> pType <* p= <*> pLam
              <* pi! "in" <*> pLam

  pArg = _,_ <$ p[ <*> pi <* p: <*> pType <* p]

  pApp = apps <$> pAtom <*> many pAtom

  pAtom =
    natrec <$ pi! "natrec" <*> pType₁ +++
    mkVar <$> pi +++
    lit   <$> pn +++
    paren pLam

parseTerm : String → Maybe RawTerm
parseTerm s = parse! pLam (lex s)

-- Examples --
-- private
--   ex₁ ex₂ ex₃ ex₄ : String
--   ex₁ = "λ (f : nat → nat) → f (f 4)"
--   ex₂ = "λ (n : nat) → suc (suc n)"
--   ex₃ = "(" & ex₂ & ") 5"

  -- ex₄ = "let twice : (nat → nat) → nat → nat
  --                  = λ (f : nat → nat) -> λ (x : nat) → f (f x) in
  --        let plustwo : nat → nat
  --                    = twice suc in
  --        twice plustwo 15"
