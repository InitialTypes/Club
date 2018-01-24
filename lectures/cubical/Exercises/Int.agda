{-# OPTIONS --cubical #-}
module Int where

open import Cubical.FromStdLib hiding (_+_;_∘_)
open import Cubical.PathPrelude
open import Cubical.GradLemma
open import Cubical.PushOut renaming (primPushOutElim to PO-elim; P to PushOut)
open import Function
-- case_of : ∀ {l m} {A : Set l} {B : Set m} → A → (A → B) → B
-- case_of x f = f x

record ⊤ : Set where
  eta-equality
  constructor tt


{-
data ℤ : Set where
  neg : ℕ → ℤ
  pos : ℕ → ℤ


  only-one-zero : PathP (\ i → ℤ) (neg 0) (pos 0)

-}

{-


                    (\ _ → zero)
                ⊤ --------------> ℕ
                |                 |
                |                 |
                |                 |
   (\ _ → zero) |            -----|
                |           |     |
                v           |     v
                ℕ --------------> ℤ


-}


ℤ = PushOut (\ (x : ⊤) → zero) (\ (x : ⊤) → zero)

neg : ℕ → ℤ
neg = inl

pos : ℕ → ℤ
pos = inr

only-one-zero : neg 0 ≡ pos 0
only-one-zero = push _

test0 : ∀ (P : ℤ → Set) → P (neg 0) ≡ P (pos 0)
test0 P = (\ i → P (only-one-zero i))



ℤ-elim : ∀ {l} (P : ℤ → Set l) → (f : ∀ n → P (neg n)) → (g : ∀ n → P (pos n))
         → (q : PathP (\ i → P (only-one-zero i)) (f 0) (g 0))
         → ∀ (x : ℤ) → P x
ℤ-elim P f g eq = PO-elim _ f g \ { tt → eq}

syntax ℤ-elim P (\ x → f) (\ y → g) eq = ℤ-split P [neg x ↦ f ∣pos y ↦ g ∣ eq ]

negate : ℤ → ℤ
negate = ℤ-split _
       [neg x ↦ pos x
       ∣pos x ↦ neg x
       ∣ sym only-one-zero  ]



sucℤ : ℤ → ℤ
sucℤ = ℤ-split _
         [neg n ↦ (case n of λ where
                     zero    → pos 1
                     (suc m) → neg m)
         ∣pos n ↦ pos (suc n)
         ∣ refl
         ]


predℤ : ℤ → ℤ
predℤ = ℤ-split _
         [neg n ↦ neg (suc n)
         ∣pos n ↦ (case n of λ where
                     zero    → neg 1
                     (suc m) → pos m)
         ∣ refl
         ]

suc-pred : ∀ x → sucℤ (predℤ x) ≡ x
suc-pred = ℤ-split (λ z → sucℤ (predℤ z) ≡ z)
              [neg n ↦ refl
              ∣pos n ↦ aux n
              ∣ ( (\ { i j → only-one-zero (i ∧ j) } ) )
              ]
 where
   aux : ∀ n → sucℤ (predℤ (pos n)) ≡ pos n
   aux zero = only-one-zero
   aux (suc n) = refl

pred-suc : ∀ x → predℤ (sucℤ x) ≡ x
pred-suc = ℤ-split (λ z → predℤ (sucℤ z) ≡ z)
              [neg n ↦ aux n
              ∣pos n ↦ refl
              ∣ (\ { i j → only-one-zero (i ∨ ~ j) })
              ]
 where
   aux : ∀ n → predℤ (sucℤ (neg n)) ≡ neg n
   aux zero = sym only-one-zero
   aux (suc n) = refl


_+pos_ : ℤ → ℕ → ℤ
x +pos zero = x
x +pos suc n = sucℤ (x +pos n)

lemma-pos : ∀ x n → predℤ x +pos n ≡ predℤ (x +pos n)
lemma-pos x zero = refl
lemma-pos x (suc n) = trans (cong sucℤ (lemma-pos x n))
                     (trans (suc-pred (x +pos n)) (sym (pred-suc (x +pos n))))

_-pos_ : ℤ → ℕ → ℤ
x -pos zero = x
x -pos suc n = predℤ (x -pos n)

lemma-neg : ∀ x n → sucℤ x -pos n ≡ sucℤ (x -pos n)
lemma-neg x zero = refl
lemma-neg x (suc n) = trans (cong predℤ (lemma-neg x n)) (sym ((trans (suc-pred (x -pos n)) (sym (pred-suc (x -pos n))))))




_+_ : ℤ → ℤ → ℤ
_+_ x = ℤ-split _
         [neg n ↦ x -pos n
         ∣pos n ↦ x +pos n
         ∣ refl
         ]

_-_ : ℤ → ℤ → ℤ
_-_ x y = x + negate y

infixr 20 _+_ _-_

proof : ∀ a b → (a +pos b) -pos b ≡ a
proof a zero = refl
proof a (suc b) = trans (cong predℤ (lemma-neg (a +pos b) b)) (trans (pred-suc ((a +pos b) -pos b)) (proof a b))

proof2 : ∀ a b → (a -pos b) +pos b ≡ a
proof2 a zero = refl
proof2 a (suc b) = trans (cong sucℤ (lemma-pos (a -pos b) b)) (trans (suc-pred ((a -pos b) +pos b)) (proof2 a b))

cancel : ∀ a b → (a + b) - b ≡ a
cancel a = ℤ-split (λ z → (a + z) - z ≡ a)
         [neg b ↦ proof2 a b
         ∣pos b ↦ proof a b
         ∣ refl
         ]
