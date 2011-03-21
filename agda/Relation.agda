
module Relation where

open import Logic
open import Function

Relation : Set -> Set -> Set1
Relation A B = A -> B -> Set

RelationOn : Set -> Set1
RelationOn A = Relation A A

record Order {A : Set} (op : RelationOn A) : Set where
    field
        refl  : ∀ {i} -> op i i
        trans : ∀ {a b c} -> op a b -> op b c -> op a c

record TotalOrder {A : Set} (op : RelationOn A) : Set where
    field
        base  : Order op
        total : ∀ {a b} -> op a b ∨ op b a

record DecidableOrder {A : Set} (op : RelationOn A) : Set where
    field
        base   : TotalOrder op
        decide : (a b : A) -> op a b ∨ ¬ op a b

trichotomy : {A : Set}{op : RelationOn A}{a b : A} ->
             TotalOrder op -> ¬ (op b a) -> op a b
trichotomy {a = a} {b = b} ord !b<=a with TotalOrder.total ord {a} {b}
... | orLeft a<=b = a<=b
... | orRight b<=a = False-elim $ !b<=a b<=a

trichotomy' : {A : Set}{op : RelationOn A}{a b : A} ->
              DecidableOrder op -> ¬ op b a -> op a b
trichotomy' = trichotomy ∘ DecidableOrder.base

