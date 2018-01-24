{-# OPTIONS --cubical #-}
module Abs where

open import Int
open import Cubical.FromStdLib hiding (_+_;_∘_)
open import Cubical.PathPrelude
open import Cubical.GradLemma
open import Cubical.PushOut renaming (primPushOutElim to PO-elim; P to PushOut)
open import Function

abs : ℤ → ℕ
abs = ℤ-split _
         [neg x ↦ {!!}
         ∣pos y ↦ {!!}
         ∣ {!!}  ]


data Sign : Set where
  positive negative : Sign

sign : ℤ → Sign
sign = {!!}


signed : Sign → ℕ → ℤ
signed positive n = pos n
signed negative n = neg n


lemma : ∀ x → x ≡ signed (sign x) (abs x)
lemma = {!!}

-- Bonus (using transp and cong): prove basic injectivity and impossibility properties
negative≢positive : negative ≡ positive → ⊥
negative≢positive eq = {!!}

neg≢pos : ∀ {x y} → neg (suc x) ≡ pos y → ⊥
neg≢pos eq = negative≢positive {!!}


-- (hint: abs)
neg-inj : ∀ {x y} → neg x ≡ neg y → x ≡ y
neg-inj = ?

pos-inj : ∀ {x y} → pos x ≡ pos y → x ≡ y
pos-inj = ?
