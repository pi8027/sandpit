
{-# OPTIONS --universe-polymorphism #-}

module Relation.Order where

open import Level
open import Logic
open import Function
open import Types

record Order {i : Level} {A : Set i} (op : RelationOn A) : Set i where
    field
        refl  : ∀ {i} -> op i i
        trans : ∀ {a b c} -> op a b -> op b c -> op a c

record TotalOrder {i : Level} {A : Set i} (op : RelationOn A) : Set i where
    field
        base  : Order op
        total : ∀ {a b} -> op a b ∨ op b a

record DecidableOrder {i : Level} {A : Set i} (op : RelationOn A) : Set i where
    field
        base   : TotalOrder op
        decide : (a b : A) -> op a b ∨ ¬ op a b

trichotomy : ∀ {i : Level}{A : Set i}{op : RelationOn A}{a b : A} ->
             TotalOrder op -> ¬ (op b a) -> op a b
trichotomy {a = a} {b} ord !b<=a with TotalOrder.total ord {a} {b}
... | orLeft a<=b = a<=b
... | orRight b<=a = ⊥-elim $ !b<=a b<=a

trichotomy' : ∀ {i : Level}{A : Set i}{op : RelationOn A}{a b : A} ->
              DecidableOrder op -> ¬ op b a -> op a b
trichotomy' order !b<=a = trichotomy (DecidableOrder.base order) !b<=a

