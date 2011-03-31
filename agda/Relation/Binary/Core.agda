
{-# OPTIONS --universe-polymorphism #-}

module Relation.Binary.Core where

open import Level

REL : ∀ {i j} → Set i → Set j → (k : Level) → Set (i ⊔ j ⊔ succ k)
REL A B k = A → B → Set k

Rel : ∀ {i} → Set i → (j : Level) → Set (i ⊔ succ j)
Rel A j = REL A A j

