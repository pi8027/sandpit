
module Relation.Equal where

open import Relation

data _==_ {A : Set} : RelationOn A where
    ==refl : {a : A} -> a == a

record Equal {A : Set} (eq : RelationOn A) : Set where
    field
        refl : ∀ {a} -> eq a a
        sym : ∀ {a b} -> eq b a -> eq a b
        trans : ∀ {a b c} -> eq a b -> eq b c -> eq a c

==sym : ∀ {A}{a b : A} -> b == a -> a == b
==sym ==refl = ==refl

==trans : ∀ {A}{a b c : A} -> a == b -> b == c -> a == c
==trans ==refl ==refl = ==refl

==Equal : {A : Set} -> Equal {A} _==_
==Equal {A} = record { refl = ==refl; sym = ==sym; trans = ==trans}
