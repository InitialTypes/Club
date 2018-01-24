{-# OPTIONS --cubical #-}

module Stream where

open import Cubical.FromStdLib using (_×_; ℕ; zero; suc)
open import Cubical.PathPrelude


record Stream (A : Set) : Set where
  coinductive
  constructor _,_
  field
    head : A
    tail : Stream A

open Stream

mapS : ∀ {A B} → (A → B) → Stream A → Stream B
head (mapS f xs) = f (head xs)
tail (mapS f xs) = mapS f (tail xs)


mapS-id : ∀ {A} {xs : Stream A} → mapS (λ x → x) xs ≡ xs
head (mapS-id {xs = xs} i) = {!!}
tail (mapS-id {xs = xs} i) = {!!}


Stream-η : ∀ {A} {xs : Stream A} → xs ≡ (head xs , tail xs)
head (Stream-η {A} {xs} i) = ?
tail (Stream-η {A} {xs} i) = ?
