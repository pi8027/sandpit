
module Mergesort where

open import Logic
open import Function
open import Relation
open import Nat
open import List
open import OList
open import Permutation

merge : {A : Set}{op : RelationOn A}{len : Nat} ->
        (order : DecidableOrder op) -> (xs ys : [ A ]) ->
        {eq : NatEq len (length xs + length ys)} -> [ A ]
merge order [] ys = ys
merge {len = succ len} order (x :: xs) [] {eqSucc eq} =
    x :: merge {len = len} order xs [] {eq}
merge {len = succ len} order (x :: xs) (y :: ys) {eqSucc eq}
    with DecidableOrder.decide order x y
... | orLeft _ = x :: merge order xs (y :: ys) {eq}
... | orRight _ = y :: merge order (x :: xs) ys
    {natEqTrans eq (succAREq {length xs} natEqRefl natEqRefl)}
merge {len = zero} _ (_ :: _) _ {()}

merge_ordered : {A : Set}{op : RelationOn A}{b : A}{len : Nat} ->
                (order : DecidableOrder op) -> (xs ys : [ A ]) ->
                ListIsOrdered order b xs -> ListIsOrdered order b ys ->
                {eq : NatEq len (length xs + length ys)} ->
                ListIsOrdered order b (merge order xs ys {eq})
merge_ordered order [] ys p1 p2 = p2
merge_ordered {len = succ len} order (x :: xs) [] (orderedCons .x p1 p2) p3 {eqSucc eq} =
    orderedCons x p1 $ merge order ordered xs [] p2 orderedNull
merge_ordered {len = succ len} order (x :: xs) (y :: ys)
    (orderedCons .x p1 p2) (orderedCons .y p3 p4) {eqSucc eq}
        with DecidableOrder.decide order x y
... | orLeft x<=y = orderedCons x p1 $
    merge_ordered {len = len} order xs (y :: ys) p2 (orderedCons y x<=y p4) {eq}
... | orRight !x<=y = orderedCons y p3 $ merge_ordered {len = len}
    order (x :: xs) ys (orderedCons x (trichotomy' order !x<=y) p2) p4
        {natEqTrans eq (succAREq {length xs} natEqRefl natEqRefl)}
merge_ordered {len = zero} _ (_ :: _) _ _ _ {()}

merge_permutation :
    {A : Set}{op : RelationOn A}{len : Nat} ->
    (order : DecidableOrder op) -> (xs ys : [ A ]) ->
    {eq : NatEq len (length xs + length ys)} ->
    Permutation (xs ++ ys) (merge order xs ys {eq})
merge_permutation order [] ys = permRefl
merge_permutation {len = succ len} order (x :: xs) [] {eqSucc eq} =
    permSkip $ merge order permutation xs []
merge_permutation {A = A} {len = succ len} order (x :: xs) (y :: ys) {eqSucc eq}
    with DecidableOrder.decide order x y
... | orLeft x<=y = permSkip $ merge_permutation {len = len} order xs (y :: ys) {eq}
... | orRight !x<=y = permTrans (move {xs = x :: xs}) $ permSkip $
    merge_permutation {len = len} order (x :: xs) ys
        {natEqTrans eq (succAREq {length xs} natEqRefl natEqRefl)} where
    move : {y : A}{xs ys : [ A ]} -> Permutation (xs ++ (y :: ys)) (y :: xs ++ ys)
    move {xs = []} = permRefl
    move {xs = x :: xs} = permTrans (permSkip (move {xs = xs})) permSwap
merge_permutation {len = zero} _ (_ :: _) _ {()}