
{-# OPTIONS --universe-polymorphism #-}

module Relation.Binary.Order where

open import Level
open import Logic
open import Function
open import Data.Empty
open import Relation.Binary.Core
open import Relation.Binary.Class

record IsPreorder {a ℓ₁ ℓ₂} {A : Set a} (_≈_ : Rel A ℓ₁) (_≤_ : Rel A ℓ₂) :
                  Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    constructor isPreorder
    
    field
        equiv : IsEquivalence _≈_
        refl  : _≈_ ⇒ _≤_
        trans : Transitive _≤_

record IsPartialOrder {a ℓ₁ ℓ₂} {A : Set a} (_≈_ : Rel A ℓ₁) (_≤_ : Rel A ℓ₂) :
                      Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    constructor isPartialOrder
    
    field
        preorder : IsPreorder _≈_ _≤_
        antisym  : Antisymmetric _≈_ _≤_

record IsTotalOrder {a ℓ₁ ℓ₂} {A : Set a} (_≈_ : Rel A ℓ₁) (_≤_ : Rel A ℓ₂) :
                  Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    constructor isTotalOrder
    field
        partialorder : IsPartialOrder _≈_ _≤_
        total        : Total _≤_

record IsDecTotalOrder {a ℓ₁ ℓ₂} {A : Set a} (_≈_ : Rel A ℓ₁) (_≤_ : Rel A ℓ₂) :
                     Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    constructor isDecTotalOrder
    field
        totalorder : IsTotalOrder _≈_ _≤_
        ≈decide    : Decidable _≈_
        ≤decide    : Decidable _≤_

