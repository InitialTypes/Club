module Ucwf where

open import Level renaming (zero to lzero ; suc to  lsuc)
open import Agda.Primitive
open import Data.Nat renaming (ℕ to Nat) using (zero ; suc)
open import Relation.Binary using (Rel ; IsEquivalence ; Setoid)

-----------------------------------------------------------------------------
-- The sorts, operator symbols, and axioms of a ucwf

record Ucwf : Set₁ where
  infix 4 _≈_
  infix 4 _≋_
  infix 8 _∘_
  
  field

    -- Objects of the base category are natural numbers
   
    -- Terms and substitutions (sorts)
    Tm   : Nat → Set lzero
    Sub  : Nat → Nat → Set lzero

    -- two relations regarding equality of terms and substitutions
    _≈_   : ∀ {n} → Rel (Tm n) lzero
    _≋_   : ∀ {m n} → Rel (Sub m n) lzero

    IsEquivT : ∀ {n} → IsEquivalence (_≈_ {n})
    IsEquivS : ∀ {m n} → IsEquivalence (_≋_ {m} {n})

    -- operators
    
    id     : ∀ {n} → Sub n n
    _∘_    : ∀ {m n k} → Sub n k → Sub m n → Sub m k
    _[_]   : ∀ {m n} → Tm n → Sub m n → Tm m
    <>     : ∀ {m} → Sub m zero
    <_,_>  : ∀ {m n} → Sub m n → Tm m → Sub m (suc n)
    p      : ∀ {n} → Sub (suc n) n
    q      : ∀ {n} → Tm (suc n)
    
    -- ucwf axioms

    -- zero length id is the empty substitution
    
    id₀ : id {0} ≋ <>

    -- <> is a a left zero for composition
  
    left-zero : ∀ {m n} (ts : Sub m n) → <> ∘ ts ≋ <>

    -- extended identity is the projection morphism with the last variable

    idExt : ∀ {n} → id {suc n} ≋ < p , q >

    -- category of substitutions
             
    idL : ∀ {m n} (ts : Sub m n) → id ∘ ts ≋ ts
             
    idR : ∀ {m n} (ts : Sub m n) → ts ∘ id ≋ ts
             
    assoc : ∀ {m n κ ι} (ts : Sub n κ)
              (us : Sub m n) (vs : Sub ι m) → (ts ∘ us) ∘ vs ≋ ts ∘ (us ∘ vs)

    -- Substituting in id doesn't affect terms
 
    subId : ∀ {n} (t : Tm n) → t [ id ] ≈ t

    -- p is the first projection

    pCons : ∀ {n κ} (ts : Sub n κ) t → p ∘ < ts , t > ≋ ts

    -- q is the second projection

    qCons : ∀ {m n} (ts : Sub n m) t → q [ < ts , t > ] ≈ t

    -- Substituting under a composition

    subComp : ∀ {m n κ} (ts : Sub m n) (us : Sub κ m) t
              → t [ ts ∘ us ] ≈ t [ ts ] [ us ]

    -- Composing with an extended substitution

    compExt : ∀ {m n} (ts : Sub n m) (us : Sub m n) t
              → < ts , t > ∘ us ≋ < ts ∘ us , t [ us ] >
             
    -- congruence rules for operators
    
    cong-<,> : ∀ {m n} {ts us : Sub m n} {t u}
               → t ≈ u
               → ts ≋ us
               → < ts , t > ≋ < us , u >
                
    cong-sub : ∀ {m n} {ts us : Sub m n} {t u}
               → t ≈ u
               → ts ≋ us
               → t [ ts ] ≈ u [ us ]
                
    cong-∘ : ∀ {m n k} {ts vs : Sub n k} {us zs : Sub m n}
             → ts ≋ vs
             → us ≋ zs
             → ts ∘ us ≋ vs ∘ zs

  ⇑ : ∀ {m n} (ts : Sub m n) → Sub (suc m) (suc n)
  ⇑ ts = < ts ∘ p , q >

  weaken : ∀ {m} → Tm m → Tm (suc m)
  weaken = _[ p ]

record Lambda-ucwf : Set₁ where
  field
    ucwf : Ucwf   
  open Ucwf ucwf public
  field

    -- λ abstraction and application

    lam : ∀ {n} → Tm (suc n) → Tm n
    app : ∀ {n} → Tm n → Tm n → Tm n

    -- substituting under app and lam
    
    subApp : ∀ {n m} (ts : Sub m n) t u → app (t [ ts ]) (u [ ts ]) ≈ (app t u) [ ts ]
    
    subLam : ∀ {n m} (ts : Sub m n) t → lam t [ ts ] ≈ lam (t [ ⇑ ts ])
    
    cong-lam : ∀ {n} {t u : Tm (suc n)}
               → t ≈ u
               → lam t ≈ lam u
              
    cong-app : ∀ {n} {t u t′ u′ : Tm n}
               → t ≈ t′
               → u ≈ u′
               → app t u ≈ app t′ u′

-- Extending the ucwf with lambdas up to β and η

record Lambda-βη-ucwf : Set₁ where
  field
    lambda-ucwf : Lambda-ucwf 

  open Lambda-ucwf lambda-ucwf

  field

   -- beta and eta equalities

    β : ∀ {n} {t : Tm (suc n)} {u} → app (lam t) u ≈ t [ < id , u > ]
         
    η : ∀ {n} {t : Tm n} → lam (app (weaken t) q) ≈ t
    
