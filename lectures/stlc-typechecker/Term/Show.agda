
module Term.Show where

open import Prelude

open import Type
open import Term

private
  showType : Nat → Type → ShowS
  showType p nat      = showString "nat"
  showType p (a => b) = showParen (p >? 7) $ showType 8 a ∘ showString " → " ∘ showType 7 b

instance
  ShowType : Show Type
  ShowType = record { showsPrec = showType }

private
  showRaw : Nat → RawTerm → ShowS
  showRaw p (var x)     = showString x
  showRaw p (lit n)     = shows n
  showRaw p suc         = showString "suc"
  showRaw p (app e e₁)  = showParen (p >? 9) $ showRaw 9 e ∘ showString " " ∘ showRaw 10 e₁
  showRaw p (lam x a e) = showParen (p >? 0) $ showString ("λ (" & x & " : ")
                                             ∘ shows a ∘ showString ") → " ∘ showRaw 0 e
  showRaw p (natrec A)  = showParen (p >? 9) $ showString "natrec " ∘ showsPrec 9 A

instance
  ShowRaw : Show RawTerm
  ShowRaw = record { showsPrec = showRaw }

  ShowTerm : ∀ {Γ a} → Show (Term Γ a)
  ShowTerm = ShowBy forgetTypes
