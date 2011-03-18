
{-# OPTIONS --termination-depth=10 #-}

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

omerge : {A : Set}{op : RelationOn A}{b : A} ->
         (order : DecidableOrder op) ->
         (xs ys : OList order b) -> OList order b
omerge {A} {op} {b} order l1 l2
        with OList.l l1 | OList.o l1 | OList.l l2 | OList.o l2
... | [] | _ | l | o = record {l = l ; o = o}
... | l | o | [] | _ = record {l = l ; o = o}
... | (x :: xs) | orderedCons .x p1 p2 | (y :: ys) | orderedCons .y p3 p4 =
    caseord order x y
    (\ x<=y -> x :# p1 #: omerge order
        record {l = xs ; o = p2}
        record {l = y :: ys ; o = orderedCons y x<=y p4})
    (\ !x<=y -> y :# p3 #: omerge order
        record {l = x :: xs ; o = orderedCons x (trichotomy' order !x<=y) p2}
        record {l = ys ; o = p4})

