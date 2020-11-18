-- Interpret the CCCInternalLanguage in an arbitrary CCC

open import CCC as _ using (CCC)

module CCC.Sound {o m e} (C : CCC o m e) where

  open module Cat = CCC C using (Ob; Unit; Prod; Arr)

  open import Types
  open import CCCInternalLanguage

  ⟦_⟧ : Ty → Ob  -- \[[   \]]
  ⟦ 𝟙 ⟧     = Unit
  ⟦ a ⇒ b ⟧ = Arr ⟦ a ⟧ ⟦ b ⟧
  ⟦ a * b ⟧ = Prod ⟦ a ⟧ ⟦ b ⟧

  ⦅_⦆ : ∀{a b} → Hom a b → Cat.Hom ⟦ a ⟧ ⟦ b ⟧  -- \((  \))
  ⦅ id ⦆       = Cat.id _
  ⦅ f ∘ g ⦆    = Cat.comp ⦅ f ⦆ ⦅ g ⦆
  ⦅ fst ⦆      = Cat.π₁
  ⦅ snd ⦆      = Cat.π₂
  ⦅ pair f g ⦆ = Cat.pair ⦅ f ⦆ ⦅ g ⦆
  ⦅ unit ⦆     = Cat.unit _
  ⦅ curry f ⦆  = Cat.curry ⦅ f ⦆
  ⦅ eval ⦆     = Cat.eval

  ⟪_⟫ : ∀{a b} {f g : Hom a b} → f ~ g → Cat.Eq ⦅ f ⦆ ⦅ g ⦆  -- \<<  \>>
  ⟪ id-l ⟫          = Cat.id-l _
  ⟪ id-r ⟫          = Cat.id-r _
  ⟪ assoc ⟫         = Cat.assoc _ _ _
  ⟪ fst-pair ⟫      = Cat.β-π₁
  ⟪ snd-pair ⟫      = Cat.β-π₂
  ⟪ id-pair ⟫       = Cat.eq-sym Cat.pair-π
  ⟪ pair-comp ⟫     = Cat.pair-nat _ _ _
  ⟪ unit ⟫          = Cat.unit-unique _
  ⟪ eval-curry ⟫    = Cat.β-eval _
  ⟪ curry-eval ⟫    = Cat.curry-eval
  ⟪ curry-comp ⟫    = Cat.curry-nat _ _
  ⟪ eq-comp e e' ⟫  = Cat.comp-cong ⟪ e ⟫ ⟪ e' ⟫
  ⟪ eq-pair e e' ⟫  = Cat.pair-cong ⟪ e ⟫ ⟪ e' ⟫
  ⟪ eq-curry e ⟫    = Cat.curry-cong ⟪ e ⟫
  ⟪ eq-refl ⟫       = Cat.eq-refl
  ⟪ eq-sym e ⟫      = Cat.eq-sym ⟪ e ⟫
  ⟪ eq-trans e e' ⟫ = Cat.eq-trans ⟪ e ⟫ ⟪ e' ⟫
