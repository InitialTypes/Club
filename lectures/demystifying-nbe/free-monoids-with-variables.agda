module free-monoids-with-variables where

-- Variation of `combinatory-system-t.agda` (Nachi, 2019,
-- [Demystifying NbE](https://github.com/InitialTypes/Club/wiki/Abstracts.2019.DemystifyingNbE))
-- for the theory of monoids over a set of generators or primitive
-- operations.

module Normalization (X : Set) where
  open import Data.Product
    using (_×_; _,_)
  open import Data.Unit
    using (⊤; tt)

  open import Level
    using    ()
    renaming (zero to ℓ0) -- \ell

  open import Relation.Binary
    using (Preorder; Setoid)
  open Preorder
    using    (Carrier)
    renaming (refl to ≤-refl; trans to ≤-trans) -- \leq4
  open Setoid
    using    (Carrier)
    renaming (refl to ≋-refl; sym to ≋-sym; trans to ≋-trans) -- \~~~

  import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
  import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties as StarProperties

  import Relation.Binary.Construct.Closure.Symmetric as SymClosure

  import Relation.Binary.Construct.Closure.Equivalence as EqClosure
  open import Relation.Binary.Construct.Closure.Equivalence.Properties
    using    ()
    renaming (a—↠b⇒a↔b to ⟶⋆⇒∼; a—↠b⇒b↔a to ⟶⋆⇒∼˘)

  open import Relation.Binary.PropositionalEquality
    using    (_≡_)
    renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong; cong₂ to ≡-cong₂; subst to ≡-subst; isEquivalence to ≡-equiv)
  import Relation.Binary.PropositionalEquality.Properties as Equality

  import Relation.Binary.Reasoning.Preorder as PreorderReasoning
  import Relation.Binary.Reasoning.Setoid as SetoidReasoning

  infixr 20 _•_
  infix  19 _⟶_ _⟶⋆_ _∼_
  infixl 4  _,_
  infix  4  ≤-syntax ≋-syntax
  infix  3  _⊢Var_ _⊢_ _⊢Ren_ _⊢Sub_ ⊢⟶∶-syntax ⊢⟶⋆∶-syntax ⊢∼∶-syntax _⊢Ne_ _⊢Ne'_ _⊢Nf_

  ≤-syntax : (A : Preorder ℓ0 ℓ0 ℓ0) → (x y : A .Carrier) → Set -- \leq4
  ≤-syntax A = A .Preorder._∼_
  syntax ≤-syntax A x y = x ≤[ A ] y

  ≤-refl[_] : (A : Preorder ℓ0 ℓ0 ℓ0) → ∀ (x : A .Carrier) → x ≤[ A ] x
  ≤-refl[ A ] _x = Preorder.refl A

  ≤-reflexive[_] : (A : Preorder ℓ0 ℓ0 ℓ0) → ∀ {x y : A .Carrier} (x≈y : A .Preorder._≈_ x y) → x ≤[ A ] y
  ≤-reflexive[ A ] = Preorder.reflexive A

  ≤-reflexive˘[_] : (A : Preorder ℓ0 ℓ0 ℓ0) → ∀ {x y : A .Carrier} (y≈x : A .Preorder._≈_ y x) → x ≤[ A ] y
  ≤-reflexive˘[ A ] y≈x = Preorder.reflexive A (Preorder.Eq.sym A y≈x)

  ≤-trans[_] : (A : Preorder ℓ0 ℓ0 ℓ0) → ∀ {x y z : A .Carrier} (x≤y : x ≤[ A ] y) (y≤z : y ≤[ A ] z) → x ≤[ A ] z
  ≤-trans[ A ] = Preorder.trans A

  ≋-syntax : (A : Setoid ℓ0 ℓ0) → (x y : A .Carrier) → Set -- \~~~
  ≋-syntax A = A .Setoid._≈_
  syntax ≋-syntax A x y = x ≋[ A ] y

  ≋-refl[_] : (A : Setoid ℓ0 ℓ0) → ∀ (x : A .Carrier) → x ≋[ A ] x
  ≋-refl[ A ] _x = A .Setoid.refl

  ≋-reflexive[_] : (A : Setoid ℓ0 ℓ0) → ∀ {x y : A .Carrier} (x≡y : x ≡ y) → x ≋[ A ] y
  ≋-reflexive[ A ] = Setoid.reflexive A

  ≋-sym[_] : (A : Setoid ℓ0 ℓ0) → ∀ {x y : A .Carrier} → x ≋[ A ] y → y ≋[ A ] x
  ≋-sym[ A ] = A .Setoid.sym

  ≋-trans[_] : (A : Setoid ℓ0 ℓ0) → ∀ {x y z : A .Carrier} (x≋y : x ≋[ A ] y) (y≋z : y ≋[ A ] z) → x ≋[ A ] z
  ≋-trans[ A ] = A .Setoid.trans

  ≋-trans˘[_] : (A : Setoid ℓ0 ℓ0) → ∀ {x y z : A .Carrier} (y≋x : y ≋[ A ] x) (y≋z : y ≋[ A ] z) → x ≋[ A ] z
  ≋-trans˘[ A ] y≋x y≋z = ≋-trans[ A ] (≋-sym[ A ] y≋x) y≋z

  -- TODO: add to stdlib
  module _ where
    open import Data.Sum using (inj₁; inj₂)
    open import Relation.Binary using (Rel; IsEquivalence; _=[_]⇒_)
    open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)

    -- A generalised variant of fold.
    gfold : ∀ {i j t p} {I : Set i} {J : Set j} {T : Rel I t} {P : Rel J p}
            (P-equiv : IsEquivalence P) →
            (f : I → J) →
            T =[ f ]⇒ P →
            EqClosure.EqClosure T =[ f ]⇒ P
    gfold P-equiv f g ε               = P-equiv .IsEquivalence.refl
    gfold P-equiv f g ((inj₁ x) ◅ xs) = P-equiv .IsEquivalence.trans (g x)                              (gfold P-equiv f g xs)
    gfold P-equiv f g ((inj₂ x) ◅ xs) = P-equiv .IsEquivalence.trans (P-equiv .IsEquivalence.sym (g x)) (gfold P-equiv f g xs)

  -- Types
  data Ty : Set where
    ∗ : Ty -- \ast

  variable
    a b c : Ty

  -- Contexts
  data Ctx : Set where
    []  : Ctx
    _,_ : (Γ : Ctx) → (a : Ty) → Ctx

  variable
    Γ Γ' Γ'' : Ctx
    Δ Δ' Δ'' : Ctx
    Θ Θ' Θ'' : Ctx

  -- Variables
  data Var : (Γ : Ctx) → (a : Ty) → Set

  _⊢Var_ = Var

  data Var where
    zero :

           ----------------
           Γ , a ⊢Var a

    succ :
           (n : Γ ⊢Var a) →
           ----------------
           Γ , b ⊢Var a

  variable
    n m : Var Γ a

  -- Terms
  data Tm : (Γ : Ctx) → (a : Ty) → Set

  _⊢_ = Tm

  data Tm where
    var :
          (n : Γ ⊢Var a) →
          ----------------
          Γ ⊢ a

    ⌜_⌝ : -- \cul \cur
          (x : X) →
          ----------------
          Γ ⊢ ∗

    _•_ : -- \bub
          (t : Γ ⊢ ∗) →
          (u : Γ ⊢ ∗) →
          ----------------
          Γ ⊢ ∗

    e :

          ----------------
          Γ ⊢ ∗

  variable
    t t' t'' : Tm Γ a
    u u' u'' : Tm Γ a
    v v' v'' : Tm Γ a

  -- Renamings
  data Ren : (Δ Γ : Ctx) → Set

  _⊢Ren_ = Ren

  data Ren where
    tt  :

          ----------------
          Δ ⊢Ren []

    _,_ :
          (r : Δ ⊢Ren Γ) →
          (n : Δ ⊢Var a) →
          ----------------
          Δ ⊢Ren Γ , a

  renVar : (r : Ren Δ Γ) → (n : Var Γ a) → Var Δ a
  renVar (_r , n)  zero     = n
  renVar (r  , _n) (succ m) = renVar r m

  renRen : (r' : Ren Θ Δ) → (r : Ren Δ Γ) → Ren Θ Γ
  renRen _r' tt      = tt
  renRen r'  (r , n) = renRen r' r , renVar r' n
  _∙ᵣ_ = renRen -- \. \_r
  _∘ᵣ_ = λ {Θ} {Δ} {Γ} r r' → renRen {Θ} {Δ} {Γ} r' r -- \circ \_r

  wkRen[_] : (a : Ty) → (r : Ren Δ Γ) → Ren (Δ , a) Γ
  wkRen[_] _a tt      = tt
  wkRen[_] a  (r , n) = wkRen[ a ] r , succ n
  wkRen = λ {Δ} {Γ} {a} → wkRen[_] {Δ} {Γ} a

  idRen[_] : (Γ : Ctx) → Ren Γ Γ
  idRen[ [] ]    = tt
  idRen[ Γ , a ] = wkRen[ a ] idRen[ Γ ] , zero
  idRen = λ {Γ} → idRen[ Γ ]

  pRen[_] : (a : Ty) → Ren (Γ , a) Γ
  pRen[ a ] = wkRen[ a ] idRen
  pRen = λ {Γ} {a} → pRen[_] {Γ} a

  renTm : (r : Ren Γ' Γ) → (t : Tm Γ a) → Tm Γ' a
  renTm r  (var n) = var (renVar r n)
  renTm _r ⌜ x ⌝   = ⌜ x ⌝
  renTm r  (t • u) = renTm r t • renTm r u
  renTm _r e       = e

  renVar-pres-wk : ∀ (r : Ren Γ' Γ) → (n : Var Γ a) → renVar (wkRen[ b ] r) n ≡ succ (renVar r n)
  renVar-pres-wk (r , m) zero     = ≡-refl
  renVar-pres-wk (r , m) (succ n) = renVar-pres-wk r n

  renVar-pres-id : ∀ (n : Var Γ a) → renVar idRen n ≡ n
  renVar-pres-id zero     = ≡-refl
  renVar-pres-id (succ n) = ≡-trans (renVar-pres-wk idRen n) (≡-cong succ (renVar-pres-id n))

  renTm-pres-id : ∀ (t : Tm Γ a) → renTm idRen t ≡ t
  renTm-pres-id (var n) = ≡-cong var (renVar-pres-id n)
  renTm-pres-id ⌜ x ⌝   = ≡-refl
  renTm-pres-id (t • u) = ≡-cong₂ _•_ (renTm-pres-id t) (renTm-pres-id u)
  renTm-pres-id e       = ≡-refl

  -- Substitutions
  data Sub : (Δ Γ : Ctx) → Set

  _⊢Sub_ = Sub

  data Sub where
    tt  :

          ----------------
          Δ ⊢Sub []

    _,_ :
          (s : Δ ⊢Sub Γ) →
          (t : Δ ⊢    a) →
          ----------------
          Δ ⊢Sub Γ , a

  variable
    s s' s'' : Sub Δ Γ

  embRen : (r : Ren Γ' Γ) → Sub Γ' Γ
  embRen tt      = tt
  embRen (r , n) = embRen r , var n

  idSub[_] : (Γ : Ctx) → Sub Γ Γ
  idSub[ Γ ] = embRen idRen[ Γ ]
  idSub = λ {Γ} → idSub[ Γ ]

  substVar : (s : Sub Δ Γ) → (n : Var Γ a) → Tm Δ a
  substVar (s , t) zero     = t
  substVar (s , t) (succ n) = substVar s n

  substTm : (s : Sub Δ Γ) → (t : Tm Γ a) → Tm Δ a
  substTm s  (var n) = substVar s n
  substTm _s ⌜ x ⌝   = ⌜ x ⌝
  substTm s  (t • u) = substTm s t • substTm s u
  substTm _s e       = e

  substSub : (s' : Sub Θ Δ) → (s : Sub Δ Γ) → Sub Θ Γ
  substSub s' tt      = tt
  substSub s' (s , t) = substSub s' s , substTm s' t
  _∙ₛ_ = substSub -- \. \_s
  _∘ₛ_ = λ {Θ} {Δ} {Γ} s s' → substSub {Θ} {Δ} {Γ} s' s -- \circ \_s

  substVar-pres-ren : ∀ (r : Ren Γ' Γ) → (n : Var Γ a) → substVar (embRen r) n ≡ var (renVar r n)
  substVar-pres-ren (r , n) zero     = ≡-refl
  substVar-pres-ren (r , m) (succ n) = substVar-pres-ren r n

  substTm-pres-ren : ∀ (r : Ren Γ' Γ) → (t : Tm Γ a) → substTm (embRen r) t ≡ renTm r t
  substTm-pres-ren r (var n) = substVar-pres-ren r n
  substTm-pres-ren r ⌜ x ⌝   = ≡-refl
  substTm-pres-ren r (t • u) = ≡-cong₂ _•_ (substTm-pres-ren r t) (substTm-pres-ren r u)
  substTm-pres-ren r e       = ≡-refl

  substTm-pres-id : ∀ (t : Tm Γ a) → substTm idSub t ≡ t
  substTm-pres-id t = ≡-trans (substTm-pres-ren idRen t) (renTm-pres-id t)

  -- Reduction
  data _⟶_ : {Γ : Ctx} → {a : Ty} → (t t' : Tm Γ a) → Set -- \-->

  ⊢⟶∶-syntax = λ Γ a t t' → _⟶_ {Γ} {a} t t' -- \vdash \--> \:
  syntax ⊢⟶∶-syntax Γ a t t' = Γ ⊢ t ⟶ t' ∶ a

  data _⟶_ where
    unit-left :
                  (t : Γ ⊢ ∗) →
                  ---------------------------------
                  Γ ⊢ e • t ⟶ t ∶ ∗

    unit-right :
                  (t : Γ ⊢ ∗) →
                  ---------------------------------
                  Γ ⊢ t • e ⟶ t ∶ ∗

    assoc-right :
                  (t u v : Γ ⊢ ∗) →
                  ---------------------------------
                  Γ ⊢ (t • u) • v ⟶ t • (u • v) ∶ ∗

    cong-left :
                  (u    : Γ ⊢ ∗) →
                  (t⟶t' : Γ ⊢ t ⟶ t' ∶ ∗) →
                  ---------------------------------
                  Γ ⊢ t • u ⟶ t' • u ∶ ∗

    cong-right :
                  (t    : Γ ⊢ ∗) →
                  (u⟶u' : Γ ⊢ u ⟶ u' ∶ ∗) →
                  ---------------------------------
                  Γ ⊢ t • u ⟶ t • u' ∶ ∗

  _⟶⋆_ : (t t' : Tm Γ a) → Set -- \--> \star
  _⟶⋆_ = Star.Star _⟶_

  ⊢⟶⋆∶-syntax = λ Γ a t t' → _⟶⋆_ {Γ} {a} t t' -- \vdash \--> \star \:
  syntax ⊢⟶⋆∶-syntax Γ a t t' = Γ ⊢ t ⟶⋆ t' ∶ a

  Tm-preorder : (Γ : Ctx) → (a : Ty) → Preorder _ _ _
  Tm-preorder Γ a = StarProperties.preorder (_⟶_ {Γ} {a})

  module _ {Γ : Ctx} {a : Ty} where
    open Preorder (Tm-preorder Γ a) using () renaming (refl to ⟶⋆-refl; reflexive to ⟶⋆-reflexive; trans to ⟶⋆-trans) public

    ⟶⋆-reflexive˘ : {t t' : Tm Γ a} → (t'≡t : t' ≡ t) → t ⟶⋆ t'
    ⟶⋆-reflexive˘ t'≡t = ⟶⋆-reflexive (≡-sym t'≡t)

  module _ where
    unit-left⋆ :
                      (t : Γ ⊢ ∗) →
                      ----------------------------------
                      Γ ⊢ e • t ⟶⋆ t ∶ ∗

    unit-right⋆ :
                      (t : Γ ⊢ ∗) →
                      ----------------------------------
                      Γ ⊢ t • e ⟶⋆ t ∶ ∗

    assoc-right⋆ :
                      (t u v : Γ ⊢ ∗) →
                      ----------------------------------
                      Γ ⊢ (t • u) • v ⟶⋆ t • (u • v) ∶ ∗

    ⟶⋆-cong-•-left :
                      (u     : Γ ⊢ ∗)          →
                      (t⟶⋆t' : Γ ⊢ t ⟶⋆ t' ∶ ∗) →
                      ----------------------------------
                      Γ ⊢ t • u ⟶⋆ t' • u ∶ ∗

    ⟶⋆-cong-•-right :
                      (t     : Γ ⊢ ∗)          →
                      (u⟶⋆u' : Γ ⊢ u ⟶⋆ u' ∶ ∗) →
                      ----------------------------------
                      Γ ⊢ t • u ⟶⋆ t • u' ∶ ∗

    ⟶⋆-cong-• :
                      (t⟶⋆t' : Γ ⊢ t ⟶⋆ t' ∶ ∗) →
                      (u⟶⋆u' : Γ ⊢ u ⟶⋆ u' ∶ ∗) →
                      ----------------------------------
                      Γ ⊢ t • u ⟶⋆ t' • u' ∶ ∗

    unit-left⋆ t                            = Star.return (unit-left t)
    unit-right⋆ t                           = Star.return (unit-right t)
    assoc-right⋆ t u v                      = Star.return (assoc-right t u v)
    ⟶⋆-cong-•-left u                        = Star.gmap (_• u) (cong-left u)
    ⟶⋆-cong-•-right t                       = Star.gmap (t •_) (cong-right t)
    ⟶⋆-cong-• {t' = t'} {u = u} t⟶⋆t' u⟶⋆u' = ⟶⋆-trans (⟶⋆-cong-•-left u t⟶⋆t') (⟶⋆-cong-•-right t' u⟶⋆u')

  -- Conversion
  _∼_ : (t u : Tm Γ a) → Set -- \~
  _∼_ = EqClosure.EqClosure _⟶_

  ⊢∼∶-syntax = λ Γ a t t' → _∼_ {Γ} {a} t t' -- \vdash \--> \~ \:
  syntax ⊢∼∶-syntax Γ a t t' = Γ ⊢ t ∼ t' ∶ a

  Tm-setoid : (Γ : Ctx) → (a : Ty) → Setoid _ _
  Tm-setoid Γ a = EqClosure.setoid (_⟶_ {Γ} {a})

  module _ {Γ : Ctx} {a : Ty} where
    open Setoid (Tm-setoid Γ a) using () renaming (refl to ∼-refl; reflexive to ∼-reflexive; sym to ∼-sym; trans to ∼-trans) public

    ∼-reflexive˘ : {t t' : Tm Γ a} → (t'≡t : t' ≡ t) → t ∼ t'
    ∼-reflexive˘ t'≡t = ∼-reflexive (≡-sym t'≡t)

  module _ where
    private
      -- TODO: add to stdlib
      open import Data.Sum using (inj₁)

      return : (t⟶t' : t ⟶ t') → t ∼ t'
      return t⟶t' = Star.return (inj₁ t⟶t')

    unit-left∼ :
                     (t : Γ ⊢ ∗) →
                     ---------------------------------
                     Γ ⊢ e • t ∼ t ∶ ∗

    unit-right∼ :
                     (t : Γ ⊢ ∗) →
                     ---------------------------------
                     Γ ⊢ t • e ∼ t ∶ ∗

    assoc-right∼ :
                     (t u v : Γ ⊢ ∗) →
                     ---------------------------------
                     Γ ⊢ (t • u) • v ∼ t • (u • v) ∶ ∗

    ∼-cong-•-left :
                     (u    : Γ ⊢ ∗)          →
                     (t∼t' : Γ ⊢ t ∼ t' ∶ ∗) →
                     ---------------------------------
                     Γ ⊢ t • u ∼ t' • u ∶ ∗

    ∼-cong-•-right :
                     (t    : Γ ⊢ ∗)          →
                     (u∼u' : Γ ⊢ u ∼ u' ∶ ∗) →
                     ---------------------------------
                     Γ ⊢ t • u ∼ t • u' ∶ ∗

    ∼-cong-• :
                     (t∼t' : Γ ⊢ t ∼ t' ∶ ∗) →
                     (u∼u' : Γ ⊢ u ∼ u' ∶ ∗) →
                     ---------------------------------
                     Γ ⊢ t • u ∼ t' • u' ∶ ∗

    unit-left∼ t                         = return (unit-left t)
    unit-right∼ t                        = return (unit-right t)
    assoc-right∼ t u v                   = return (assoc-right t u v)
    ∼-cong-•-left u                      = EqClosure.gmap (_• u) (cong-left u)
    ∼-cong-•-right t                     = EqClosure.gmap (t •_) (cong-right t)
    ∼-cong-• {t' = t'} {u = u} t∼t' u∼u' = ∼-trans (∼-cong-•-left u t∼t') (∼-cong-•-right t' u∼u')

  -- Normal forms (either a (nonempty) right-associated list (cons
  -- list) of generators or the unit; we just as well could have
  -- picked left association (snoc lists) or lists that end/begin with
  -- the unit)
  data Ne  : (Γ : Ctx) → (a : Ty) → Set
  data Ne' : (Γ : Ctx) → (a : Ty) → Set
  data Nf  : (Γ : Ctx) → (a : Ty) → Set

  _⊢Ne_  = Ne
  _⊢Ne'_ = Ne'
  _⊢Nf_  = Nf

  data Ne where
    var :
          (n : Γ ⊢Var a) →
          ----------------
          Γ ⊢Ne a

    ⌜_⌝ :
          (x : X) →
          ----------------
          Γ ⊢Ne ∗

  data Ne' where
    ne  :
          (n : Γ ⊢Ne a) →
          ----------------
          Γ ⊢Ne' a

    _•_ :
          (n : Γ ⊢Ne  ∗) →
          (m : Γ ⊢Ne' ∗) →
          ----------------
          Γ ⊢Ne' ∗

  data Nf where
    ne' :
          (n : Γ ⊢Ne' a) →
          ----------------
          Γ ⊢Nf a

    e   :

          ----------------
          Γ ⊢Nf ∗

  Nf-preorder : (Γ : Ctx) → (a : Ty) → Preorder ℓ0 ℓ0 ℓ0
  Nf-preorder = λ Γ a → Equality.preorder (Nf Γ a)

  Nf-setoid : (Γ : Ctx) → (a : Ty) → Setoid ℓ0 ℓ0
  Nf-setoid Γ a = Equality.setoid (Nf Γ a)

  embNe : (n : Ne Γ a) → Tm Γ a
  embNe (var n) = var n
  embNe ⌜ x ⌝   = ⌜ x ⌝

  embNe' : (n : Ne' Γ a) → Tm Γ a
  embNe' (ne n)  = embNe n
  embNe' (n • m) = embNe n • embNe' m

  embNf : (n : Nf Γ a) → Tm Γ a
  embNf (ne' n) = embNe' n
  embNf e       = e

  renNe : (r : Ren Γ' Γ) → (n : Ne Γ a) → Ne Γ' a
  renNe r  (var n) = var (renVar r n)
  renNe _r ⌜ x ⌝   = ⌜ x ⌝

  renNe' : (r : Ren Γ' Γ) → (n : Ne' Γ a) → Ne' Γ' a
  renNe' r (ne n)  = ne (renNe r n)
  renNe' r (n • m) = renNe r n • renNe' r m

  renNf : (r : Ren Γ' Γ) → (n : Nf Γ a) → Nf Γ' a
  renNf r (ne' n) = ne' (renNe' r n)
  renNf r e       = e

  -------------------------------
  -- Normalization by Evaluation
  -------------------------------

  module EvalPresheaf
    (⟦∗⟧Ty    : (Γ : Ctx) → Setoid ℓ0 ℓ0)
    (⟦∗⟧renTy : {Γ' Γ : Ctx} → (r : Ren Γ' Γ) → (xs : ⟦∗⟧Ty Γ .Carrier) → ⟦∗⟧Ty Γ' .Carrier)
    (⟦_⟧X     : {Γ : Ctx} → (x : X) → ⟦∗⟧Ty Γ .Carrier)
    (_++_     : {Γ : Ctx} → (n m : ⟦∗⟧Ty Γ .Carrier) → ⟦∗⟧Ty Γ .Carrier)
    (nil      : {Γ : Ctx} → ⟦∗⟧Ty Γ .Carrier)
    where

    -- interpretation of types
    ⟦_⟧Ty-setoid : (a : Ty) → (Γ : Ctx) → Setoid ℓ0 ℓ0 -- \[[ \]]
    ⟦ ∗ ⟧Ty-setoid = ⟦∗⟧Ty

    ⟦_⟧Ty : (a : Ty) → (Γ : Ctx) → Set
    ⟦ a ⟧Ty Γ = ⟦ a ⟧Ty-setoid Γ .Carrier

    ⟦_⟧renTy : (a : Ty) → (r : Ren Γ' Γ) → ⟦ a ⟧Ty Γ → ⟦ a ⟧Ty Γ'
    ⟦ ∗ ⟧renTy = ⟦∗⟧renTy

    -- interpretation of contexts
    ⟦_⟧Ctx : (Δ : Ctx) → (Γ : Ctx) → Set
    ⟦ []    ⟧Ctx _Γ = ⊤
    ⟦ Δ , a ⟧Ctx Γ  = ⟦ Δ ⟧Ctx Γ × ⟦ a ⟧Ty Γ

    ⟦_⟧renCtx : (Δ : Ctx) → (r : Ren Γ' Γ) → ⟦ Δ ⟧Ctx Γ → ⟦ Δ ⟧Ctx Γ'
    ⟦ []    ⟧renCtx r tt       = tt
    ⟦ Δ , a ⟧renCtx r (γ , xs) = ⟦ Δ ⟧renCtx r γ , ⟦ a ⟧renTy r xs

    -- interpretation of variables
    ⟦_⟧Var : (n : Var Δ a) → (δ : ⟦ Δ ⟧Ctx Γ) → ⟦ a ⟧Ty Γ
    ⟦ zero   ⟧Var (_δ , xs) = xs
    ⟦ succ n ⟧Var (δ , _xs) = ⟦ n ⟧Var δ

    -- interpretation of terms
    ⟦_⟧Tm : (t : Tm Δ a) → (δ : ⟦ Δ ⟧Ctx Γ) → ⟦ a ⟧Ty Γ
    ⟦ var n ⟧Tm δ  = ⟦ n ⟧Var δ
    ⟦ ⌜ x ⌝ ⟧Tm _δ = ⟦ x ⟧X
    ⟦ t • u ⟧Tm δ  = ⟦ t ⟧Tm δ ++ ⟦ u ⟧Tm δ
    ⟦ e     ⟧Tm _δ = nil

    -- interpretation of substitutions
    ⟦_⟧Sub : (s : Sub Θ Δ) → (θ : ⟦ Θ ⟧Ctx Γ) → ⟦ Δ ⟧Ctx Γ
    ⟦ tt    ⟧Sub _θ = tt
    ⟦ s , t ⟧Sub θ  = ⟦ s ⟧Sub θ , ⟦ t ⟧Tm θ

    module Soundness
      (++-identityˡ : {Γ : Ctx} → (n : ⟦∗⟧Ty Γ .Carrier) → nil ++ n ≋[ ⟦∗⟧Ty Γ ] n)
      (++-identityʳ : {Γ : Ctx} → (n : ⟦∗⟧Ty Γ .Carrier) → n ++ nil ≋[ ⟦∗⟧Ty Γ ] n)
      (++-assoc     : {Γ : Ctx} → (n m o : ⟦∗⟧Ty Γ .Carrier) → (n ++ m) ++ o ≋[ ⟦∗⟧Ty Γ ] n ++ (m ++ o))
      (++-cong      : {Γ : Ctx} → {n n' m m' : ⟦∗⟧Ty Γ .Carrier} → (n≋n' : n ≋[ ⟦∗⟧Ty Γ ] n') → (m≋m' : m ≋[ ⟦∗⟧Ty Γ ] m') → n ++ m ≋[ ⟦∗⟧Ty Γ ] n' ++ m')
      where
      soundness : ∀ {t t' : Tm Δ a} → (t⟶t' : t ⟶ t') → ∀ (δ : ⟦ Δ ⟧Ctx Γ) → ⟦ t ⟧Tm δ ≋[ ⟦ a ⟧Ty-setoid Γ ] ⟦ t' ⟧Tm δ
      soundness (unit-left t)       δ = ++-identityˡ (⟦ t ⟧Tm δ)
      soundness (unit-right t)      δ = ++-identityʳ (⟦ t ⟧Tm δ)
      soundness (assoc-right t u v) δ = ++-assoc (⟦ t ⟧Tm δ) (⟦ u ⟧Tm δ) (⟦ v ⟧Tm δ)
      soundness (cong-left  u t⟶t') δ = ++-cong (soundness t⟶t' δ) (≋-refl[ ⟦∗⟧Ty _ ] (⟦ u ⟧Tm δ))
      soundness (cong-right t u⟶u') δ = ++-cong (≋-refl[ ⟦∗⟧Ty _ ] (⟦ t ⟧Tm δ)) (soundness u⟶u' δ)

      ⟦⟧Tm-pres-≋ : ∀ {t t' : Tm Δ a} → (t≋t' : t ≋[ Tm-setoid Δ a ] t') → ∀ (δ : ⟦ Δ ⟧Ctx Γ) → ⟦ t ⟧Tm δ ≋[ ⟦ a ⟧Ty-setoid Γ ] ⟦ t' ⟧Tm δ
      ⟦⟧Tm-pres-≋ {a = a} {Γ} {t} {t'} t≋t' δ = gfold (⟦ a ⟧Ty-setoid Γ .Setoid.isEquivalence) (λ t → ⟦ t ⟧Tm δ) (λ t⟶t' → soundness t⟶t' δ) t≋t'

  module EvalTm
    where
      open EvalPresheaf (λ Γ → Tm-setoid Γ ∗) renTm ⌜_⌝ _•_ e
      open Soundness unit-left∼ unit-right∼ assoc-right∼ ∼-cong-•

  module EvalLogicalRelation
    (⟦∗⟧Ty    : (Γ : Ctx) → (t : Tm Γ ∗) → Set)
    (⟦_⟧X     : {Γ : Ctx} → (x : X) → ⟦∗⟧Ty Γ ⌜ x ⌝)
    (_++_     : {Γ : Ctx} → {t u : Tm Γ ∗} → (p : ⟦∗⟧Ty Γ t) → (q : ⟦∗⟧Ty Γ u) → ⟦∗⟧Ty Γ (t • u))
    (nil      : {Γ : Ctx} → ⟦∗⟧Ty Γ e)
    where
    -- interpretation of types
    ⟦_⟧Ty : (a : Ty) → (Γ : Ctx) → (t : Tm Γ a) → Set
    ⟦ ∗ ⟧Ty = ⟦∗⟧Ty

    -- interpretation of contexts
    ⟦_⟧Ctx : (Δ : Ctx) → (Γ : Ctx) → (s : Sub Γ Δ) → Set
    ⟦ []    ⟧Ctx _Γ tt      = ⊤
    ⟦ Δ , a ⟧Ctx Γ  (s , t) = ⟦ Δ ⟧Ctx Γ s × ⟦ a ⟧Ty Γ t

    -- interpretation of variables
    ⟦_⟧Var : (n : Var Δ a) → (s : Sub Γ Δ) → (δ : ⟦ Δ ⟧Ctx Γ s) → ⟦ a ⟧Ty Γ (substVar s n)
    ⟦ zero   ⟧Var (_s , t) (δ , p)  = p
    ⟦ succ n ⟧Var (s , _t) (δ , _p) = ⟦ n ⟧Var s δ

    -- interpretation of terms
    --
    --
    -- ⟦ Δ ⟧Ctx -----> ⟦ a ⟧Ty
    --  |               |
    --  |    ⟦ t ⟧Tm    |
    --  v               v
    -- Sub Δ --------> Tm a
    ⟦_⟧Tm : (t : Tm Δ a) → (s : Sub Γ Δ) → (δ : ⟦ Δ ⟧Ctx Γ s) → ⟦ a ⟧Ty Γ (substTm s t)
    ⟦ var n ⟧Tm s  δ  = ⟦ n ⟧Var s δ
    ⟦ ⌜ x ⌝ ⟧Tm _s _δ = ⟦ x ⟧X
    ⟦ t • u ⟧Tm s  δ  = ⟦ t ⟧Tm s δ ++ ⟦ u ⟧Tm s δ
    ⟦ e     ⟧Tm _s _δ = nil

    -- interpretation of substitutions
    ⟦_⟧Sub : (s' : Sub Θ Δ) → (s : Sub Γ Θ) → (δ : ⟦ Θ ⟧Ctx Γ s) → ⟦ Δ ⟧Ctx Γ (substSub s s')
    ⟦ tt     ⟧Sub s δ = tt
    ⟦ s' , t ⟧Sub s δ = ⟦ s' ⟧Sub s δ , ⟦ t ⟧Tm s δ

  module _ where
    private
      _++'_ : (n m : Ne' Γ ∗) → Ne' Γ ∗
      ne n     ++' m = n • m
      (n • m') ++' m = n • (m' ++' m)

    _++_ : (n m : Nf Γ ∗) → Nf Γ ∗
    ne' n ++ ne' m = ne' (n ++' m)
    ne' n ++ e     = ne' n
    e     ++ m     = m

    ++-identityˡ : (n : Nf Γ ∗) → e ++ n ≡ n
    ++-identityˡ n = ≡-refl

    ++-identityʳ : (n : Nf Γ ∗) → n ++ e ≡ n
    ++-identityʳ (ne' n) = ≡-refl
    ++-identityʳ e       = ≡-refl

    private
      ++'-assoc : (n m o : Ne' Γ ∗) → (n ++' m) ++' o ≡ n ++' (m ++' o)
      ++'-assoc (ne n)   m o = ≡-refl
      ++'-assoc (n • n') m o = ≡-cong (n •_) (++'-assoc n' m o)

    ++-assoc : (n m o : Nf Γ ∗) → (n ++ m) ++ o ≡ n ++ (m ++ o)
    ++-assoc (ne' n) (ne' m) (ne' o) = ≡-cong ne' (++'-assoc n m o)
    ++-assoc (ne' n) (ne' m) e       = ≡-refl
    ++-assoc (ne' n) e       o       = ≡-refl
    ++-assoc e       m       o       = ≡-refl

    [_] : (x : X) → Nf Γ ∗
    [ x ] = ne' (ne ⌜ x ⌝)

    module _ where
      open EvalPresheaf (λ Γ → Nf-setoid Γ ∗) renNf [_] _++_ e
      open Soundness ++-identityˡ ++-identityʳ ++-assoc (≡-cong₂ _++_)

      -- reflection functions
      reflectTy : (a : Ty) → ⟦ a ⟧Ty (Γ , a)
      reflectTy ∗ = ne' (ne (var zero))

      reflectCtx : (Γ : Ctx) → ⟦ Γ ⟧Ctx Γ
      reflectCtx []      = tt
      reflectCtx (Γ , a) = ⟦ Γ ⟧renCtx pRen[ a ] (reflectCtx Γ) , reflectTy a

      -- reification function
      reifyTy : (a : Ty) → ⟦ a ⟧Ty Γ → Nf Γ a
      reifyTy ∗ n = n

      cong-reifyTy : ∀ (a : Ty) → {x y : ⟦ a ⟧Ty Γ} → x ≋[ ⟦ a ⟧Ty-setoid Γ ] y → reifyTy a x ≡ reifyTy a y
      cong-reifyTy ∗ n≡m = n≡m

      -- normalization function
      norm : (t : Tm Γ a) → Nf Γ a
      norm {Γ} {a} t = reifyTy a (⟦ t ⟧Tm (reflectCtx Γ))

      norm-complete : ∀ {t t' : Tm Γ a} → (t⟶t' : t ⟶ t') → norm t ≡ norm t'
      norm-complete {Γ} {a} t⟶t' = cong-reifyTy a (soundness t⟶t' (reflectCtx Γ))

    module _ where
      private
        embNe'-pres-• : ∀ (n m : Ne' Γ ∗) → embNe' n • embNe' m ⟶⋆ embNe' (n ++' m)
        embNe'-pres-• (ne n)   m = ⟶⋆-refl
        embNe'-pres-• (n • n') m = ⟶⋆-trans (assoc-right⋆ (embNe n) (embNe' n') (embNe' m)) (⟶⋆-cong-•-right (embNe n) (embNe'-pres-• n' m))

        embNf-pres-• : ∀ (n m : Nf Γ ∗) → embNf n • embNf m ⟶⋆ embNf (n ++ m)
        embNf-pres-• (ne' n) (ne' m) = embNe'-pres-• n m
        embNf-pres-• (ne' n) e       = unit-right⋆ (embNe' n)
        embNf-pres-• e       m       = unit-left⋆ (embNf m)

      open EvalLogicalRelation
        (λ _Γ t → t ⟶⋆ embNf (norm t))
        (λ _x → ⟶⋆-refl)
        (λ {_Γ} {t} {u} t⟶⋆normt u⟶⋆normu → ⟶⋆-trans (⟶⋆-cong-• t⟶⋆normt u⟶⋆normu) (embNf-pres-• (norm t) (norm u)))
        ⟶⋆-refl

      private
        principal-lemma : ∀ (Γ : Ctx) → ⟦ Γ ⟧Ctx Γ idSub -- XXX: name
        principal-lemma = {!!}

        fundamental-theorem : ∀ (t : Tm Γ a) → ⟦ a ⟧Ty Γ t
        fundamental-theorem {Γ} {a} t = ≡-subst (⟦ a ⟧Ty Γ) (substTm-pres-id t) (⟦ t ⟧Tm idSub (principal-lemma Γ))

        corollary : ∀ (t : Tm Γ a) → t ⟶⋆ embNf (norm t)
        corollary {_Γ} {∗} t = fundamental-theorem t

      norm-adequate : ∀ {t u : Tm Γ a} → norm t ≡ norm u → t ∼ u
      norm-adequate {Γ} {a} {t} {u} normt≡normu = let open SetoidReasoning (Tm-setoid Γ a) in begin
        t               ≈⟨ ⟶⋆⇒∼ (corollary t) ⟩
        embNf (norm t)  ≡⟨ ≡-cong embNf normt≡normu ⟩
        embNf (norm u)  ≈⟨ ⟶⋆⇒∼˘ (corollary u) ⟩
        u               ∎

module Example where
  open import Data.Nat using (ℕ)

  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

  open Normalization ℕ

  ex : Tm ([] , ∗ , ∗) ∗
  ex = (((⌜ 5 ⌝ • var zero) • var (succ zero)) • (⌜ 7 ⌝ • e)) • (e • ⌜ 59 ⌝)

  _ : embNf (norm ex) ≡ ⌜ 5 ⌝ • (var zero • (var (succ zero) • (⌜ 7 ⌝ • ⌜ 59 ⌝)))
  _ = refl
