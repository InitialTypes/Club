module Code where

open import Agda.Builtin.Nat using (_-_)
open import Data.Bool using (if_then_else_; not)
open import Data.List
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_,_; ∃; _×_)
open import Data.Nat
open import Relation.Nullary.Negation

tail₁ : {A : Set} → List A → List A
tail₁  []        = []
tail₁  (x ∷ xs)  = xs

tail₂ : {A : Set} → List A → Maybe (List A)
tail₂  []        = nothing
tail₂  (x ∷ xs)  = just xs

data NonEmpty {A : Set} : List A → Set where
  _∷_ : (x : A) (xs : List A) → NonEmpty (x ∷ xs)

tail₃ : {A : Set} → {xs : List A} → NonEmpty xs → List A
tail₃ (y ∷ ys) = ys

ack : ℕ → ℕ → ℕ
ack  0        m        = suc m
ack  (suc n)  0        = ack n 1
ack  (suc n)  (suc m)  = ack n (ack (suc n) m)

module _ {A : Set} (_<_ : A → A → Set) where
  variable
    x x' y y' z : A

  data _<Lex_ : (A × A) → (A × A) → Set where
    left  : x < x' → (x , y) <Lex (x' , z)
    right : y < y' → (x , y) <Lex (x  , y')

merge : List ℕ → List ℕ → List ℕ
merge  []          ys        = ys
merge  xs@(_ ∷ _)  []        = xs
merge  (x ∷ xs)    (y ∷ ys)  = if (x <ᵇ y) then (x ∷ merge xs (y ∷ ys)) else (y ∷ merge (x ∷ xs) ys)

f₁ : {A : Set} → List A → List A → List A
f₁  []        ys  = []
f₁  (x ∷ xs)  ys  = f₁ ys xs

g : {A : Set} → List A → List A
g  []            = []
g  (x ∷ [])      = []
g  (x ∷ y ∷ xs)  = g (x ∷ xs)

module _ {A : Set} (_<_ : A → A → Set) where
  data Acc (a : A) : Set where
    acc : (rs : ∀ x → x < a → Acc x) → Acc a

  wf : Set
  wf = ∀ a → Acc a

  module _ {P : A → Set} (e : ∀ x → (∀ y → y < x → P y) → P x) where
    wfr : {a : A} → Acc a → P a
    wfr acca@(acc rs) = e _ (λ x x<a → wfr (rs x x<a))

infix 4 _⊰_
_⊰_ : List ℕ → List ℕ → Set
xs ⊰ ys = length xs < length ys

allacc : wf _⊰_
allacc = {!!}

prlt : ∀ x xs → filter (λ y → y ≤? x) xs ⊰ x ∷ xs
prlt = {!!}

prge : ∀ x xs → filter (λ y → y >? x) xs ⊰ x ∷ xs
prge = {!!}

quicksort₁ : List ℕ → List ℕ
quicksort₁ xs = wfr _⊰_ qswfr (allacc xs)
  where
    qswfr : ∀ xs → (∀ ys → ys ⊰ xs → List ℕ) → List ℕ
    qswfr  []         h  = []
    qswfr  (x ∷ xs0)  h  = h (filter (λ y → y ≤? x) xs0) (prlt x xs0) ++ x ∷ h (filter (λ y → y >? x) xs0) (prge x xs0)

data dom : List ℕ → Set where
  dom-[]  : dom []
  dom-∷   : ∀ {x} {xs} → dom (filter (λ y → y <? x) xs) → dom (filter (λ y → ¬? (y <? x)) xs) → dom (x ∷ xs)

quicksort₂ : ∀ xs → dom xs → List ℕ
quicksort₂  []        dom-[]       = []
quicksort₂  (x ∷ xs)  (dom-∷ p q)  = quicksort₂ (filter (λ y → y <? x) xs) p ++ x ∷ quicksort₂ (filter (λ y → ¬? (y <? x)) xs) q

all-dom : ∀ xs → dom xs
all-dom = {!!}

Quicksort : List ℕ → List ℕ
Quicksort xs = quicksort₂ xs (all-dom xs)

data dom-f₂ : ℕ → Set where
  dom-f₂-1  : dom-f₂ 1
  dom-f₂-s  : ∀ {n} → dom-f₂ (suc (suc n)) → dom-f₂ (suc (suc n))

f₂ : ∀ n → dom-f₂ n → ℕ
f₂  1              dom-f₂-1      = 0
f₂  (suc (suc n))  (dom-f₂-s p)  = f₂ (suc (suc n)) p

data dom-f₃ : ℕ → Set where
  dom-f₃-1 : dom-f₃ 1

f₃ : ∀ n → dom-f₃ n → ℕ
f₃ 1 dom-f₃-1 = 0

mutual
  data dom91₁ : ℕ → Set where
    dom100<  : ∀ {n} → 100 < n → dom91₁ n
    dom≤100  : ∀ {n} → n ≤ 100 → (p : dom91₁ (n + 11)) → dom91₁ (f91₁ (n + 11) p) → dom91₁ n

  f91₁ : ∀ n → dom91₁ n → ℕ
  f91₁  n  (dom100< h)      = n - 10
  f91₁  n  (dom≤100 h p q)  = f91₁ (f91₁ (n + 11) p) q

data Sorted : List ℕ → Set where
  sort-[]  : Sorted []
  sort-∷   : ∀ {x} {xs} → {!!} → Sorted (x ∷ xs)

sorted-qs : ∀ {xs} → ∀ d → Sorted (quicksort₂ xs d)
sorted-qs  dom-[]       = sort-[]
sorted-qs  (dom-∷ p q)  = let sqs-< = sorted-qs p
                              sqs-⩾ = sorted-qs q
                          in {!!}

infix 5 _↓_
data _↓_ : ℕ → ℕ → Set where
  100<  : ∀ n → 100 < n → n ↓ n - 10
  ≤100  : ∀ n x y → n ≤ 100 → n + 11 ↓ x → x ↓ y → n ↓ y

dom91₂ : ℕ → Set
dom91₂ n = ∃ (λ y → n ↓ y)

f91₂ : ∀ n → dom91₂ n → ℕ
f91₂ n (y , _) = y

{-
Termination checking fails:

data Tree (A : Set) : Set where
  tree : A → List (Tree A) → Tree A

mirror : {A : Set} → Tree A → Tree A
mirror (tree a ts) = tree a (map mirror (reverse ts))
-}

module Sized where
  open import Size

  data Tree (A : Set) (i : Size) : Set where
    tree : {j : Size< i} → A → List (Tree A j) → Tree A i

  variable
    A : Set
    i : Size

  mirror : Tree A i → Tree A i
  mirror (tree a ts) = tree a (map mirror (reverse ts))
