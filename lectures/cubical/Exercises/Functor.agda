{-# OPTIONS --cubical #-}
module Functor where

module InductiveEquality where
  open import Data.Maybe
  open import Data.Bool
  open import Data.Unit


  infix 4 _≡_
  data _≡_ {a} {A : Set a} (x : A) : A → Set a where
    refl : x ≡ x

  Id-Law : (F : Set → Set) → (∀ {A B} → (A → B) → F A → F B) → Set₁
  Id-Law F map = ∀ {A} (a : F A) → map (\ x → x) a ≡ a


  mapMaybe : ∀ {A B : Set} → (A → B) → Maybe A → Maybe B
  mapMaybe f (just x) = just (f x)
  mapMaybe f nothing  = nothing

  Maybe-Id : Id-Law Maybe mapMaybe
  Maybe-Id (just x) = refl
  Maybe-Id nothing = refl


  Reader : Set → Set → Set
  Reader r a = r → a

  Reader-Id : ∀ {r} → Id-Law (Reader r) \ f g r → f (g r)
  Reader-Id a = refl

  -- cannot prove this.
  Reader∘Maybe-Id : ∀ {R} → Id-Law (\ a → Reader R (Maybe a)) (\ f g r → mapMaybe f (g r))
  Reader∘Maybe-Id a = {!!}

  module TestCase where
    R = Bool
    A = Bool

    a : Reader Bool (Maybe ⊤)
    a true = just _
    a false = nothing

    test : (λ r → mapMaybe (λ x → x) (a r)) ≡ (\ (r : R) → a r)
    test = Reader∘Maybe-Id a


module Path where
  open import Cubical.PathPrelude
  open import Data.Maybe
  open import Data.Product

  module Laws (F : Set → Set) (map : ∀ {A B} → (A → B) → F A → F B) where
    Id-Law : Set₁
    Id-Law = ∀ {A} (a : F A) → map (\ x → x) a ≡ a

    ∘-Law : Set₁
    ∘-Law = ∀ {A B C} (g : B → C) (f : A → B) (a : F A)
            → map (\ x → g (f x)) a ≡ map g (map f a)

  open Laws

  mapMaybe : ∀ {A B : Set} → (A → B) → Maybe A → Maybe B
  mapMaybe f (just x) = just (f x)
  mapMaybe f nothing = nothing

  Maybe-Id : Id-Law Maybe mapMaybe
  Maybe-Id (just x) = refl
  Maybe-Id nothing = refl

  Maybe-∘ : ∘-Law Maybe mapMaybe
  Maybe-∘ f g x = {!!}

  Reader : Set → Set → Set
  Reader r a = r → a

  Reader-Id : ∀ {r} → Id-Law (Reader r) \ f g r → f (g r)
  Reader-Id a = refl

  Reader-∘ : ∀ {r} → ∘-Law (Reader r) \ f g r → f (g r)
  Reader-∘ f g x = {!!}

  Reader∘Maybe-Id : ∀ {R} → Id-Law (\ a → Reader R (Maybe a)) (\ f g r → mapMaybe f (g r))
  Reader∘Maybe-Id a =  \ { i → \ r → Maybe-Id (a r) i }

  Reader∘Maybe-∘ : ∀ {R} → ∘-Law (\ a → Reader R (Maybe a)) (\ f g r → mapMaybe f (g r))
  Reader∘Maybe-∘ f g a = {!!}


  -- Bonus: do the same for StateT. Consider using funExt!

  StateT : ∀ s (m : Set → Set) a → Set
  StateT s m a = s → m (s × a)

  module StateT (F : Set → Set) (map : ∀ {A B} → (A → B) → F A → F B)
                (let module LF = Laws F map) (F-id : LF.Id-Law) (F-∘ : LF.∘-Law)
                (S : Set) where

         G = StateT S F

         mapStateT : ∀ {A B : Set} → (A → B) → G A → G B
         mapStateT f x s = map (\ { (s , a) → s , f a }) (x s)

         StateT-id : Id-Law G mapStateT
         StateT-id a = {!!}

         StateT-∘ : ∘-Law G mapStateT
         StateT-∘ f g a = {!!}
