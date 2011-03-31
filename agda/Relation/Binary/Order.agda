
{-# OPTIONS --universe-polymorphism #-}

module Relation.Binary.Order where

open import Logic
open import Types
open import Function
open import Relation.Binary.Core

record Order {i} {A : Set i} (op : Rel A i) : Set i where
    constructor order
    field
        refl  : ∀ {i} → op i i
        trans : ∀ {a b c} → op a b → op b c → op a c

record TotalOrder {i} {A : Set i} (op : Rel A i) : Set i where
    constructor torder
    field
        base  : Order op
        total : ∀ {a b} → op a b ∨ op b a

record DecidableOrder {i} {A : Set i} (op : Rel A i) : Set i where
    constructor dorder
    field
        base   : TotalOrder op
        decide : (a b : A) → Decide (op a b)

trichotomy : ∀ {i} {A : Set i} {op : Rel A i} {a b : A} →
             TotalOrder op → ¬ (op b a) → op a b
trichotomy (torder _ total) b≰a = orMerge id (⊥-elim ∘ b≰a) total

trichotomy' : ∀ {i} {A : Set i} {op : Rel A i} {a b : A} →
              DecidableOrder op → ¬ op b a → op a b
trichotomy' (dorder base _) b≰a = trichotomy base b≰a

