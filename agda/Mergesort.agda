
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
          (op x y -> B) -> ((op x y -> False) -> B) -> B
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
         (n : Nat) ->
         (order : DecidableOrder op) ->
         (xs : OList order b) -> (ys : OList order b) ->
         {_ : NatEq n (olength xs + olength ys)} -> OList order b
omerge zero _ [#] [#] = [#]
omerge (succ n) order [#] (y :# yr #: ys) {eqSucc c} =
    y :# yr #: omerge n order [#] ys {c}
omerge (succ n) order (x :# xr #: xs) [#] {eqSucc c} =
    x :# xr #: omerge n order xs [#] {c}
omerge (succ n) order (x :# xr #: xs) (y :# yr #: ys) {eqSucc c} =
    caseord order x y
    (\ x<=y -> x :# xr #: omerge n order xs (y :# x<=y #: ys) {c})
    (\ !x<=y -> y :# yr #:
        omerge n order (x :# trichotomy' order !x<=y #: xs) ys
            {natEqTrans c $ succAREq' {olength xs} {olength ys}})
omerge zero _ [#] (_ :# _ #: _) {()}
omerge zero _ (_ :# _ #: _) _ {()}
omerge (succ _) _ [#] [#] {()}