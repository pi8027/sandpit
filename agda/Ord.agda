
module Ord where

Relation : Set -> Set -> Set1
Relation A B = A -> B -> Set

record OrderRelation (A : Set) (f : Relation A A) : Set where
    field
        refl : (i : A) -> f i i
        trans : (a b c : A) -> f a b -> f b c -> f a c

