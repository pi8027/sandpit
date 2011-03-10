
module Relation where

open import Logic

Relation : Set -> Set -> Set1
Relation A B = A -> B -> Set

RelationOn : Set -> Set1
RelationOn A = Relation A A

record Order {A : Set} (op : RelationOn A) : Set where
    field
        refl  : forall {i} -> op i i
        trans : forall {a b c} -> op a b -> op b c -> op a c

record TotalOrder {A : Set} (op : RelationOn A) : Set where
    field
        base  : Order op
        total : forall {a b} -> op a b \/ op b a

record DecidableOrder {A : Set} (op : RelationOn A) : Set where
    field
        base   : TotalOrder op
        decide : (a b : A) -> op a b \/ (op a b -> False)

