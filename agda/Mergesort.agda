
module Mergesort where

open import Logic
open import Function
open import Relation
open import Nat
open import List
open import Ordered
open import Permutation

merge :
    ∀ {A op len} -> DecidableOrder op ->
    (xs ys : [ A ]) -> {eq : NatEq len (length xs + length ys)} -> [ A ]
merge order [] ys = ys
merge {len = succ len} order (x :: xs) [] {eqSucc eq} =
    x :: merge {len = len} order xs [] {eq}
merge {len = succ len} order (x :: xs) (y :: ys) {eqSucc eq}
    with DecidableOrder.decide order x y
... | orLeft _ = x :: merge order xs (y :: ys) {eq}
... | orRight _ = y :: merge order (x :: xs) ys
    {natEqTrans eq (succAREq {length xs} natEqRefl natEqRefl)}
merge {len = zero} _ (_ :: _) _ {()}

merge' : ∀ {A op} -> DecidableOrder op -> [ A ] -> [ A ] -> [ A ]
merge' order xs ys = merge {len = length xs + length ys} order xs ys {natEqRefl}

merge_ordered :
    ∀ {A op b len} -> (order : DecidableOrder op) ->
    (xs ys : [ A ]) -> Ordered order b xs -> Ordered order b ys ->
    {eq : NatEq len (length xs + length ys)} ->
    Ordered order b (merge order xs ys {eq})
merge_ordered _ [] _ _ p2 = p2
merge_ordered {len = succ _}
    order (x :: xs) [] (orderedCons .x p1 p2) _ {eqSucc _} =
        orderedCons x p1 $ merge order ordered xs [] p2 orderedNull
merge_ordered {len = succ len} order (x :: xs) (y :: ys)
    (orderedCons .x p1 p2) (orderedCons .y p3 p4) {eqSucc eq}
        with DecidableOrder.decide order x y
... | orLeft x<=y = orderedCons x p1 $
    merge_ordered {len = len} order xs (y :: ys) p2 (orderedCons y x<=y p4)
... | orRight !x<=y = orderedCons y p3 $
    merge_ordered {len = len} order (x :: xs) ys
        (orderedCons x (trichotomy' order !x<=y) p2) p4
merge_ordered {len = zero} _ (_ :: _) _ _ _ {()}

merge_ordered' :
    ∀ {A op b} -> (order : DecidableOrder op) ->
    (xs ys : [ A ]) -> Ordered order b xs -> Ordered order b ys ->
    Ordered order b (merge' order xs ys)
merge_ordered' order xs ys ox oy = merge_ordered order xs ys ox oy

merge_permutation :
    ∀ {A op len} -> (order : DecidableOrder op) ->
    (xs ys : [ A ]) -> {eq : NatEq len (length xs + length ys)} ->
    Permutation (xs ++ ys) (merge order xs ys {eq})
merge_permutation order [] ys = permRefl
merge_permutation {len = succ len} order (x :: xs) [] {eqSucc eq} =
    permSkip $ merge order permutation xs []
merge_permutation {A = A} {len = succ len} order (x :: xs) (y :: ys) {eqSucc _}
    with DecidableOrder.decide order x y
... | orLeft _ = permSkip $ merge_permutation {len = len} order xs (y :: ys)
... | orRight _ = permTrans (move {xs = x :: xs}) $ permSkip $
    merge_permutation {len = len} order (x :: xs) ys where
    move : {y : A}{xs ys : [ A ]} ->
           Permutation (xs ++ (y :: ys)) (y :: xs ++ ys)
    move {xs = []} = permRefl
    move {xs = x :: xs} = permTrans (permSkip (move {xs = xs})) permSwap
merge_permutation {len = zero} _ (_ :: _) _ {()}

merge_permutation' :
    ∀ {A op} -> (order : DecidableOrder op) ->
    (xs ys : [ A ]) -> Permutation (xs ++ ys) (merge' order xs ys)
merge_permutation' order xs ys = merge_permutation order xs ys

mergePair : {A : Set}{op : RelationOn A} ->
            DecidableOrder op -> [ [ A ] ] -> [ [ A ] ]
mergePair order [] = []
mergePair order (x :: []) = x :: []
mergePair order (x :: x' :: xs) = merge' order x x' :: mergePair order xs

half : Nat -> Nat
half zero = zero
half (succ zero) = succ zero
half (succ (succ n)) = succ $ half n

natLog2 : Nat -> Nat
natLog2 zero = zero
natLog2 (succ zero) = zero
natLog2 n = succ $ natLog2 $ half n

mergePair-half :
    {A : Set}{op : RelationOn A}{order : DecidableOrder op}{l : [ [ A ] ]} ->
    NatEq (half (length l)) (length (mergePair order l))
mergePair-half {l = []} = eqZero
mergePair-half {l = _ :: []} = eqSucc eqZero
mergePair-half {l = _ :: _ :: l} = eqSucc $ mergePair-half {l = l}

mergeAll :
    ∀ {A op len} -> DecidableOrder op -> (xs : [ [ A ] ]) ->
    {eq : NatEq len (natLog2 (length xs))} -> [ A ]
mergeAll {len = zero} order [] = []
mergeAll {len = zero} order (x :: []) = x
mergeAll {len = succ len} order (x :: x' :: xs) {eqSucc eq} =
    mergeAll {len = len} order (mergePair order (x :: x' :: xs))
    {natEqTrans eq $ natEqRefl' (natLog2 ∘ succ) $ mergePair-half {l = xs}}
mergeAll {len = zero} _ (_ :: _ :: _) {()}
mergeAll {len = succ _} _ [] {()}
mergeAll {len = succ _} _ (_ :: []) {()}

mergeAll' : ∀ {A op} -> DecidableOrder op -> [ [ A ] ] -> [ A ]
mergeAll' order xs = mergeAll {len = natLog2 $ length xs} order xs {natEqRefl}

mergesort : ∀ {A op} -> DecidableOrder op -> [ A ] -> [ A ]
mergesort order xs = mergeAll' order $ map (flip _::_ []) xs

