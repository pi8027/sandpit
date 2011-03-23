
module Algorithm.Mergesort where

open import Logic
open import Function
open import Data.Nat
open import Data.List
open import Relation
open import Relation.Equal
open import Relation.Equal.Nat
open import Relation.Order
open import Relation.Order.Nat
open import Relation.Permutation
open import Group.Nat

merge :
    ∀ {A op len} -> DecidableOrder op ->
    (xs ys : [ A ]) -> {eq : len == (length xs + length ys)} -> [ A ]
merge order [] ys = ys
merge {len = succ len} order (x :: xs) [] {eq} =
    x :: merge {len = len} order xs [] {==desucc eq}
merge {len = succ len} order (x :: xs) (y :: ys) {eq}
    with DecidableOrder.decide order x y
... | orLeft _ = x :: merge {len = len} order xs (y :: ys) {==desucc eq}
... | orRight _ = y :: merge {len = len} order (x :: xs) ys
    {==trans (==desucc eq) (==sym (addSuccReflexive {length xs}))}
merge {len = zero} _ (_ :: _) _ {()}

merge' : ∀ {A op} -> DecidableOrder op -> [ A ] -> [ A ] -> [ A ]
merge' order xs ys = merge {len = length xs + length ys} order xs ys {==refl}

merge_ordered :
    ∀ {A op b len} -> (order : DecidableOrder op) ->
    (xs ys : [ A ]) -> Ordered order b xs -> Ordered order b ys ->
    {eq : len == (length xs + length ys)} ->
    Ordered order b (merge order xs ys {eq})
merge_ordered _ [] _ _ p2 = p2
merge_ordered {len = succ _}
    order (x :: xs) [] (orderedCons .x p1 p2) _ =
        orderedCons x p1 $ merge order ordered xs [] p2 orderedNull
merge_ordered {len = succ len} order (x :: xs) (y :: ys)
    (orderedCons .x p1 p2) (orderedCons .y p3 p4)
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
    (xs ys : [ A ]) -> {eq : len == (length xs + length ys)} ->
    Permutation (xs ++ ys) (merge order xs ys {eq})
merge_permutation order [] ys = permRefl
merge_permutation {len = succ len} order (x :: xs) [] =
    permSkip $ merge order permutation xs []
merge_permutation {A = A} {len = succ len} order (x :: xs) (y :: ys)
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
    ∀ {A op} -> (order : DecidableOrder op) -> (xs ys : [ A ]) ->
    Permutation (xs ++ ys) (merge' order xs ys)
merge_permutation' order xs ys = merge_permutation order xs ys

mergePair : ∀ {A op} -> DecidableOrder op -> [ [ A ] ] -> [ [ A ] ]
mergePair order [] = []
mergePair order (x :: []) = x :: []
mergePair order (x :: x' :: xs) = merge' order x x' :: mergePair order xs

<=mergePair : ∀ {A op}{order : DecidableOrder op}{l : [ [ A ] ]} ->
              length (mergePair order l) <= length l
<=mergePair {l = []} = <=zero
<=mergePair {l = _ :: []} = <=succ <=zero
<=mergePair {l = _ :: _ :: l} =
    <=succ $ <=trans (<=mergePair {l = l}) <=reflSucc

mergePair_ordered :
    ∀ {A op b} -> (order : DecidableOrder op) -> (l : [ [ A ] ]) ->
    Sequence (Ordered order b) l ->
    Sequence (Ordered order b) (mergePair order l)
mergePair_ordered order [] nullSeq = nullSeq
mergePair_ordered order (x :: []) (consSeq p nullSeq) = consSeq p nullSeq
mergePair_ordered order (x :: x' :: xs) (consSeq p (consSeq p' p'')) =
    consSeq (merge_ordered' order x x' p p') (mergePair_ordered order xs p'')

mergePair_permutation :
    ∀ {A op} -> (order : DecidableOrder op) -> (l : [ [ A ] ]) ->
    Permutation (concat l) (concat (mergePair order l))
mergePair_permutation order [] = permNull
mergePair_permutation order (x :: []) = permRefl
mergePair_permutation order (x :: x' :: xs) =
    permTrans (permSym (permAppend' {xs = x}))
    (permAppend (merge_permutation order x x') (mergePair_permutation order xs))

mergeAll : ∀ {A op n} -> DecidableOrder op -> (l : [ [ A ] ]) ->
           {rel : length l <= n} -> [ A ]
mergeAll order [] = []
mergeAll order (x :: []) = x
mergeAll {n = succ n} order (x :: x' :: xs) {<=succ rel} =
    mergeAll {n = n} order (mergePair order (x :: x' :: xs))
    {<=trans (<=succ (<=mergePair {l = xs})) rel}
mergeAll {n = zero} _ (_ :: _) {()}

mergeAll' : ∀ {A op} -> DecidableOrder op -> [ [ A ] ] -> [ A ]
mergeAll' order xs = mergeAll {n = length xs} order xs {<=refl}

mergesort : ∀ {A op} -> DecidableOrder op -> [ A ] -> [ A ]
mergesort order xs = mergeAll' order $ map (flip _::_ []) xs

