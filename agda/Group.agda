
{-# OPTIONS --universe-polymorphism #-}

module Group where

open import Level
open import Types
open import Relation.Equal

record Semigroup {i : Level} {A : Set i}
        (eq : RelationOn A) (add : BinOp A) : Set i where
    field
        base : Equal eq
        assoc : {a b c : A} -> eq (add a (add b c)) (add (add a b) c)

record CSemigroup {i : Level} {A : Set i}
        (eq : RelationOn A) (add : BinOp A) : Set i where
    field
        base : Semigroup eq add
        comm : ∀ {a b} -> eq (add a b) (add b a)

record Monoid {i : Level} {A : Set i}
        (eq : RelationOn A) (add : BinOp A) (id : A) : Set i where
    field
        base : Semigroup eq add
        idleft : ∀ {a} -> eq (add id a) a
        idright : ∀ {a} -> eq (add a id) a

record CMonoid {i : Level} {A : Set i}
        (eq : RelationOn A) (add : BinOp A) (id : A) : Set i where
    field
        base : Monoid eq add id
        comm : ∀ {a b} -> eq (add a b) (add b a)

