module ML1 where

open import Agda.Primitive  -- Universe levels

open import CCC2 as _ using (CCC2)

record ML1 o m e : Set (lsuc (o ⊔ m ⊔ e)) where
  field
    ccc : CCC2 o m e

  open CCC2 ccc public

  field
    M₀        : (a : Ob) → Ob
    eta       : (a : Ob) → Hom a (M₀ a)
    bind      : {c a b : Ob} → Hom c (M₀ a) → Hom c (Arr a (M₀ b)) → Hom c (M₀ b)
    bind-comp : {c' c a b : Ob} {ma : Hom c (M₀ a)} {k : Hom c (Arr a (M₀ b))} {h : Hom c' c}
      → Eq (comp (bind ma k) h)
           (bind (comp ma h) (comp k h))

  -- Andreas, why does the following definition cause an error if we
  -- don't bind any implicit arguments on the lhs of the equation?
  return : {c a : Ob} → Hom c (Arr a (M₀ a))
  return {_} {a} = curry (comp (eta a) π₂)

  field
    right-unital : ∀{c a} {ma : Hom c (M₀ a)}
      → Eq (bind ma return)
           ma
    left-unital  : ∀{c a b} {x : Hom c a} {k : Hom c (Arr a (M₀ b))}
      → Eq (bind (apply return x) k)
           (apply k x)
    associative  : ∀{c a b d} {ma : Hom c (M₀ a)} {k : Hom c (Arr a (M₀ b))} {l : Hom c (Arr b (M₀ d))}
      → Eq (bind ma (curry (bind (apply (comp k π₁) π₂) (comp l π₁))))
           (bind (bind ma k) l)
