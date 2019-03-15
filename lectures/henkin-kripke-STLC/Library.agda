module Library where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; cong-app; module ≡-Reasoning; subst) public
open import Function using (_∘_; id) public
open import Data.Empty public
open import Data.Product using (proj₁; proj₂; _,_; Σ; _×_) public
open import Data.Unit using (⊤) public
