module ML where

open import Agda.Primitive  -- Universe levels

open import CCC as _ using (CCC)
import Exercises.TheOneTimesAIsomorphicA as 1A=A
import Exercises.ABCIsomorphicABC as [AB]C=A[BC]

record ML o m e : Set (lsuc (o ⊔ m ⊔ e)) where
  field
    ccc : CCC o m e

  open CCC ccc public

  field
    -- Functor M
    M₀       : (a : Ob) → Ob
    M₁       : {a b : Ob} → Hom a b → Hom (M₀ a) (M₀ b)
    M₁-id    : ∀{a}
      → Eq (M₁ (id a))
           (id (M₀ a))
    M₁-comp  : ∀{a b c} {f : Hom b c} {g : Hom a b}
      → Eq (M₁ (comp f g))
           (comp (M₁ f) (M₁ g))

    -- Natural transformation η : Id → M
    eta      : (a : Ob) → Hom a (M₀ a)
    eta-nat  : ∀{a b} (f : Hom a b)
      → Eq (comp (eta b) f)
           (comp (M₁ f) (eta a))

    -- Natural transformation μ : M² → M
    mu       : (a : Ob) → Hom (M₀ (M₀ a)) (M₀ a)
    mu-nat   : ∀{a b} (f : Hom a b)
      → Eq (comp (mu b) (M₁ (M₁ f)))
           (comp (M₁ f) (mu a))

    -- Monad laws for (M,η,μ)
    mu-etaM  : ∀{a}
      → Eq (comp (mu a) (eta (M₀ a)))
           (id (M₀ a))
    mu-Meta  : ∀{a}
      → Eq (comp (mu a) (M₁ (eta a)))
           (id (M₀ a))
    mu-mu    : ∀{a}
      → Eq (comp (mu a) (mu (M₀ a)))
           (comp (mu a) (M₁ (mu a)))

    -- Strength τ for the monad (M,η,μ) over the Cartesian product -×-
    tau      : (a b : Ob) → Hom (Prod a (M₀ b)) (M₀ (Prod a b))
    tau-nat  : ∀{a a' b b'} {f : Hom a a'} {g : Hom b b'}
      → Eq (comp (tau a' b') (Prod₁ f (M₁ g)))
           (comp (M₁ (Prod₁ f g)) (tau a b))
    tau-Unit : let open 1A=A cc in ∀{a}
      → Eq (comp (tau Unit a) from)
           (M₁ from)
    tau-tau  : let open [AB]C=A[BC] cc in ∀{a b c}
      → Eq (comp (tau a (Prod b c)) (comp (Prod₁ (id a) (tau b c)) ltr))
           (comp (M₁ ltr) (tau (Prod a b) c))
    tau-eta  : ∀{a b}
      → Eq (comp (tau a b) (Prod₁ (id a) (eta b)))
           (eta (Prod a b))
    tau-mu   : ∀{a b}
      → Eq (comp (tau a b) (Prod₁ (id a) (mu b)))
           (comp (mu (Prod a b)) (comp (M₁ (tau a b)) (tau a (M₀ b))))
