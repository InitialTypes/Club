
module Term.Lex where

open import Prelude
open import Prelude.Equality.Unsafe
open import Text.Lex

data Token : Set where
  tλ t[ t] t→ t: t= : Token
  ti : String → Token
  tn : Nat → Token

ti-inj : ∀ {x y} → ti x ≡ ti y → x ≡ y
ti-inj refl = refl

tn-inj : ∀ {x y} → tn x ≡ tn y → x ≡ y
tn-inj refl = refl

private
  eqTok : (x y : Token) → Dec (x ≡ y)
  eqTok tλ tλ  = yes refl
  eqTok t→ t→ = yes refl
  eqTok t: t:  = yes refl
  eqTok t= t=  = yes refl
  eqTok t[ t[  = yes refl
  eqTok t] t]  = yes refl
  eqTok (ti x) (ti  y) with x == y
  eqTok (ti x) (ti .x) | yes refl = yes refl
  eqTok (ti x) (ti  y) | no neq   = no λ eq → neq (ti-inj eq)
  eqTok (tn m) (tn  n) with m == n
  eqTok (tn m) (tn .m) | yes refl = yes refl
  eqTok (tn m) (tn  n) | no neq   = no λ eq → neq (tn-inj eq)
  eqTok _ _ = no unsafeNotEqual

instance
  EqToken : Eq Token
  EqToken = record { _==_ = eqTok }

keywordTok : Token → String → TokenDFA Char (Maybe Token)
keywordTok t k = just t <$ keywordToken (unpackString k)

tokenSpecs : List (TokenDFA Char (Maybe Token))
tokenSpecs =
    keywordTok tλ "λ"
  ∷ keywordTok tλ "\\"
  ∷ keywordTok t[ "("
  ∷ keywordTok t] ")"
  ∷ keywordTok t→ "→"
  ∷ keywordTok t→ "->"
  ∷ keywordTok t:  ":"
  ∷ keywordTok t=  "="
  ∷ keywordTok (ti "_") "_"
  ∷ (just ∘ ti ∘ packString <$> identToken isAlpha isAlphaNum)
  ∷ (just ∘ tn <$> natToken)
  ∷ (nothing <$ matchToken isSpace)
  ∷ []

lex : String → List Token
lex = concatMap (maybe [] [_]) ∘ tokenize tokenSpecs ∘ unpackString
