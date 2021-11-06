module ChurchRosser {ℓ} {A : Set ℓ} (let Rel = A → A → Set ℓ) (R : Rel) where

open import Level using (_⊔_)

open import NewmansLemma R renaming (singl to *-singl; refl to *-refl; trans to *-trans; Joinable to _↓_)

private
  variable
    a b c : A

infix 1 _iff_

record _iff_ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field
    ltr : A → B
    rtl : B → A

-- zigzag/equivalence closure
data _⇝_ : Rel where
  nil : a ⇝ a
  zig : (r : R a b) → (rs : b ⇝ c) → a ⇝ c
  zag : (r : R b a) → (rs : b ⇝ c) → a ⇝ c

refl : a ⇝ a
refl = nil

singl : (r : R a b) → a ⇝ b
singl r = zig r refl

giz : (rs : a ⇝ b) → (r : R b c) → a ⇝ c
giz nil        r' = zig r' refl
giz (zig r rs) r' = zig r (giz rs r')
giz (zag r rs) r' = zag r (giz rs r')

gaz : (rs : a ⇝ b) → (r : R c b) → a ⇝ c
gaz nil        r' = zag r' refl
gaz (zig r rs) r' = zig r (gaz rs r')
gaz (zag r rs) r' = zag r (gaz rs r')

sym : (rs : a ⇝ b) → b ⇝ a
sym nil        = refl
sym (zig r rs) = gaz (sym rs) r
sym (zag r rs) = giz (sym rs) r

trans : (rs : a ⇝ b) → (ss : b ⇝ c) → a ⇝ c
trans nil        ss = ss
trans (zig r rs) ss = zig r (trans rs ss)
trans (zag r rs) ss = zag r (trans rs ss)

˘trans : (rs : b ⇝ a) → (ss : b ⇝ c) → a ⇝ c
˘trans rs ss = trans (sym rs) ss

trans˘ : (rs : a ⇝ b) → (ss : c ⇝ b) → a ⇝ c
trans˘ rs ss = trans rs (sym ss)

singls : (rs : R* a b) → a ⇝ b -- because `_⇝_` contains `R` and is transitive
singls nil         = refl
singls (cons r rs) = zig r (singls rs)

zigs : (rs : R* a b) → (ss : b ⇝ c) → a ⇝ c
zigs rs ss = trans (singls rs) ss

zags : (rs : R* b a) → (ss : b ⇝ c) → a ⇝ c
zags rs ss = ˘trans (singls rs) ss

-- `singls` and `trans˘` imply `_↓_ ⊆ _⇝_`, and `R` satisfies the
-- Church–Rosser property if the converse inclusion holds too

ChurchRosser = ∀ {a b} → a ⇝ b → a ↓ b

private
  ltr : ChurchRosser → ∀ {a} → Confl a
  ltr cr = {!!}

  rtl : (∀ {a} → Confl a) → ChurchRosser
  rtl cf = {!!}

goal : ChurchRosser iff ∀ {a} → Confl a
goal = ltr , rtl
