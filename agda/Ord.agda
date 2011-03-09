
module Ord where

open import Logic

Relation : Set -> Set -> Set1
Relation A B = A -> B -> Set

data Order {A : Set} (op : Relation A A) : Relation A A where
    leq : {x y : A} -> op x y -> Order op x y
    gt : {x y : A} -> (op x y -> False) -> Order op x y

record OrderLaws {A : Set} (op : Relation A A) : Set where
    field
        refl : forall {i} -> op i i
        trans : forall {a b c} -> op a b -> op b c -> op a c

