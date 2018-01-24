{-# OPTIONS --cubical #-}
module JandComp where

open import Cubical.PathPrelude hiding (sym; trans; trans')

module UsingJ where
  sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym {x = x} = pathJ (\ y _ → y ≡ x) refl _

  trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans {x = x} {z = z} = pathJ (λ y _ → y ≡ z → x ≡ z) (\ p → p) _

  trans-id : ∀ {A : Set} {x y : A} → (eq : x ≡ y) → trans eq refl ≡ eq
  trans-id {x = x} = pathJ (\ y eq → trans eq refl ≡ eq) (\ i → pathJprop (λ y _ → y ≡ x → x ≡ x) (\ p → p) i refl) _


-- (Harder)
module UsingComp where
{-

   Using i for the horizontal dimension and j for the vertical one we
   can draw the following incomplete square using the inputs for trans.

          x - - - - - - - - > z
          ^                   ^
          |                   |
          |                   |
        x |                   | q j
          |                   |
          |                   |
          |                   |
          x ----------------> y
                  p i

   "primComp" gives us the ability to complete any square and get out
   its top line, the dotted one.
   (it actually generalizes to n-cubes, depending on how many dimensions are in scope)

-}
  trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans {A} {x = x} p q = \ i → primComp (\ i → A) _

                                                 -- sides of the square
                                                 (\ { j (i = i0) → x
                                                    ; j (i = i1) → q j })

                                                 -- the base of the square
                                                 (p i)

  -- Find other ways to put p and q in an incomplete square to implement trans
  --   (hint: ~ is useful to reverse the direction of a path).
  trans' : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans' = {!!}


  -- Now we want to build an equality of equalities, i.e. a square,
  -- which we can obtain as the face of a cube (we have dimensions i,j,k).

  -- You will have to satisfy these constraints:
  -- let M = trans-id {A} {x} {y}

  --  M eq i1 j = eq j : A
  --  M eq i0 j
  --    = primComp (λ i → A) (~ j ∨ j)
  --      (λ { i (j = i0) → x ; i (j = i1) → refl i }) (eq j)
  --    : A
  --  M eq i i1 = y : A
  --  M eq i i0 = x : A

  -- Write the necessary composition term!

  -- The constrains above specify the sides of the lid of a cube, you
  -- will have to come up with the base (the opposite face) and some
  -- of the other faces on the sides.

  trans-id : ∀ {A : Set} {x y : A} → (eq : x ≡ y) → trans eq refl ≡ eq
  trans-id {A} {x} {y} eq i j = primComp {!!} {!!} (\ k → {!!}) {!!}
