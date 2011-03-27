
{-# OPTIONS --universe-polymorphism #-}

module Algorithm.Mergesort.Permutation where

open import Logic
open import Function
open import Types
open import Data.Nat
open import Data.List
open import Group.List
open import Relation.Equal
open import Relation.Order
open import Relation.Order.Nat
open import Relation.Permutation
open import Algorithm.Mergesort.Impl

merge-permutation :
    ∀ {i}{A : Set i}{op : RelationOn A}{len : Nat} ->
    (order : DecidableOrder op) -> (xs ys : [ A ]) ->
    {eq : len == (length xs + length ys)} ->
    Permutation (xs ++ ys) (merge order xs ys {eq})
merge-permutation order [] ys = eqPerm ==refl
merge-permutation {len = succ len} order (x :: xs) [] =
    permSkip $ merge-permutation order xs []
merge-permutation {A = A} {len = succ len} order (x :: xs) (y :: ys)
    with DecidableOrder.decide order x y
... | orLeft _ = permSkip $ merge-permutation {len = len} order xs (y :: ys)
... | orRight _ = permTrans (move {xs = x :: xs}) $ permSkip $
    merge-permutation {len = len} order (x :: xs) ys where
    move : {y : A}{xs ys : [ A ]} ->
           Permutation (xs ++ (y :: ys)) (y :: xs ++ ys)
    move {xs = []} = eqPerm ==refl
    move {xs = x :: xs} = permTrans (permSkip (move {xs = xs})) permSwap
merge-permutation {len = zero} _ (_ :: _) _ {()}

merge-permutation' :
    ∀ {i}{A : Set i}{op : RelationOn A} ->
    (order : DecidableOrder op) -> (xs ys : [ A ]) ->
    Permutation (xs ++ ys) (merge' order xs ys)
merge-permutation' order xs ys = merge-permutation order xs ys

mergePair-permutation :
    ∀ {i}{A : Set i}{op : RelationOn A} ->
    (order : DecidableOrder op) -> (l : [ [ A ] ]) ->
    Permutation (concat l) (concat (mergePair order l))
mergePair-permutation order [] = permNull
mergePair-permutation order (x :: []) = eqPerm ==refl
mergePair-permutation order (x :: x' :: xs) =
    permTrans (eqPerm (++assoc {a = x}))
    (permAppend (merge-permutation order x x') (mergePair-permutation order xs))

mergeAll-permutation :
    ∀ {i}{A : Set i}{op : RelationOn A}{n : Nat} ->
    (order : DecidableOrder op) -> (l : [ [ A ] ]) ->
    {rel : length l <= n} -> Permutation (concat l) (mergeAll order l {rel})
mergeAll-permutation order [] = permNull
mergeAll-permutation order (x :: []) = eqPerm ++idright
mergeAll-permutation {n = succ n} order (x :: x' :: xs) {<=succ rel} =
    permTrans (mergePair-permutation order (x :: x' :: xs))
        (mergeAll-permutation {n = n} order (mergePair order (x :: x' :: xs)))
mergeAll-permutation {n = zero} _ (_ :: _) {()}

mergeAll-permutation' :
    ∀ {i}{A : Set i}{op : RelationOn A} ->
    (order : DecidableOrder op) -> (l : [ [ A ] ]) ->
    Permutation (concat l) (mergeAll' order l)
mergeAll-permutation' order l =
    mergeAll-permutation {n = length l} order l {<=refl}

mergesort-permutation :
    ∀ {i}{A : Set i}{op : RelationOn A} ->
    (order : DecidableOrder op) -> (l : [ A ]) ->
    Permutation l (mergesort order l)
mergesort-permutation order l =
    permTrans (eqPerm p) (mergeAll-permutation' order (map (flip _::_ []) l))
    where
    p : ∀ {l} -> l == concat (map (flip _::_ []) l)
    p {[]} = ==refl
    p {x :: xs} = ==apply'' _::_ ==refl $ p {xs}
