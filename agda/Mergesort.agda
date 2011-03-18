
module Mergesort where

open import Logic
open import Function
open import Relation
open import List
open import OList
open import Nat

caseord : {A B : Set}{op : RelationOn A} ->
          DecidableOrder op -> (x y : A) ->
          (op x y -> B) -> (¬ op x y -> B) -> B
caseord order x y f g = orMerge f g $ DecidableOrder.decide order x y

merge : {A : Set}{op : RelationOn A} ->
        DecidableOrder op -> [ A ] -> [ A ] -> [ A ]
merge _ [] l = l
merge _ l [] = l
merge order (x :: xs) (y :: ys) =
    caseord order x y
        (const (x :: merge order xs (y :: ys)))
        (const (y :: merge order (x :: xs) ys))

ordmerge : {A : Set}{op : RelationOn A}{b : A}{len : Nat} ->
           (order : DecidableOrder op) -> (xs ys : OList order b) ->
           {eq : NatEq len (length (OList.l xs) + length (OList.l ys))} ->
           OList order b
ordmerge {len = zero} _ _ _ = record {l = [] ; o = orderedNull}
ordmerge {len = succ len} order l1 l2 {eq}
        with OList.l l1 | OList.o l1 | OList.l l2 | OList.o l2 | eq
... | _ | _ | [] | _ | _ = l1
... | [] | _ | _ | _ | _ = l2
... | x :: xs | orderedCons .x p1 p2 | y :: ys | orderedCons .y p3 p4 | eqSucc eq' =
    caseord order x y
    (\ x<=y -> x :# p1 #: ordmerge {len = len} order
        record { l = xs; o = p2 }
        record { l = y :: ys; o = orderedCons y x<=y p4 }
        {eq'})
    (\ !x<=y -> y :# p3 #: ordmerge {len = len} order
        record { l = x :: xs; o = orderedCons x (trichotomy' order !x<=y) p2 }
        record { l = ys; o = p4 }
        {natEqTrans eq' (succAREq' {length xs} {length ys})})