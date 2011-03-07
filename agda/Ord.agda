
module Ord where

Relation : Set -> Set -> Set1
Relation A B = A -> B -> Set

record OrderRelation {A : Set} (f : Relation A A) : Set where
    field
        refl : forall {i} -> f i i
        trans : forall {a b c} -> f a b -> f b c -> f a c

data False : Set where

data _\/_ (Left : Set) (Right : Set) : Set where
    orLeft : Left -> Left \/ Right
    orRight : Right -> Left \/ Right

record _/\_ (Left : Set) (Right : Set) : Set where
    field
        l : Left
        r : Right

data SeqOrder {A B : Set} (rela : Relation A A) (relb : Relation B B)
        : A -> B -> A -> B -> Set where
    seqOrder : forall {a1 b1 a2 b2} ->
        rela a1 a2 -> ((rela a2 a1 -> False) \/ relb b1 b2) ->
        SeqOrder rela relb a1 b1 a2 b2

seqOrderTrans :
    forall {A B : Set}{rela : Relation A A}{relb : Relation B B}{a1 b1 a2 b2 a3 b3} ->
    OrderRelation rela -> OrderRelation relb ->
    SeqOrder rela relb a1 b1 a2 b2 -> SeqOrder rela relb a2 b2 a3 b3 ->
    SeqOrder rela relb a1 b1 a3 b3
seqOrderTrans ora orb (seqOrder p1 (orLeft p2)) (seqOrder p3 _) =
    seqOrder (OrderRelation.trans ora p1 p3)
        (orLeft (\p -> p2 (OrderRelation.trans ora p3 p)))
seqOrderTrans ora orb (seqOrder p1 _) (seqOrder p2 (orLeft p3)) =
    seqOrder (OrderRelation.trans ora p1 p2)
        (orLeft (\p -> p3 (OrderRelation.trans ora p p1)))
seqOrderTrans ora orb (seqOrder p1 (orRight p2)) (seqOrder p3 (orRight p4)) =
    seqOrder (OrderRelation.trans ora p1 p3)
        (orRight (OrderRelation.trans orb p2 p4))

