
{-# OPTIONS --universe-polymorphism #-}

module Group where

open import Types
open import Relation.Binary.Core
open import Relation.Binary.Equal

record Semigroup {i} {A : Set i} (eq : Rel A i) (add : BinOp A) : Set i where
    constructor semigroup
    field
        base : Equal eq
        assoc : {a b c : A} → eq (add a (add b c)) (add (add a b) c)

record CSemigroup {i} {A : Set i} (eq : Rel A i) (add : BinOp A) : Set i where
    constructor csemigroup
    field
        base : Semigroup eq add
        comm : ∀ {a b} → eq (add a b) (add b a)

record Monoid {i} {A : Set i}
              (eq : Rel A i) (add : BinOp A) (id : A) : Set i where
    constructor monoid
    field
        base : Semigroup eq add
        idleft : ∀ {a} → eq (add id a) a
        idright : ∀ {a} → eq (add a id) a

record CMonoid {i} {A : Set i}
        (eq : Rel A i) (add : BinOp A) (id : A) : Set i where
    constructor cmonoid
    field
        base : Monoid eq add id
        comm : ∀ {a b} → eq (add a b) (add b a)

