
module Group where

open import Relation
open import Relation.Equal

BinOp : Set -> Set
BinOp A = A -> A -> A

record Semigroup {A : Set} (eq : RelationOn A) (add : BinOp A) : Set where
    field
        base : Equal eq
        assoc : {a b c : A} -> eq (add a (add b c)) (add (add a b) c)

record CSemigroup {A : Set} (eq : RelationOn A) (add : BinOp A) : Set where
    field
        base : Semigroup eq add
        comm : ∀ {a b} -> eq (add a b) (add b a)

record Monoid {A : Set} (eq : RelationOn A) (add : BinOp A) (id : A) : Set where
    field
        base : Semigroup eq add
        idleft : ∀ {a} -> eq (add id a) a
        idright : ∀ {a} -> eq (add a id) a

record CMonoid {A : Set} (eq : RelationOn A) (add : BinOp A) (id : A) :
        Set where
    field
        base : Monoid eq add id
        comm : ∀ {a b} -> eq (add a b) (add b a)

