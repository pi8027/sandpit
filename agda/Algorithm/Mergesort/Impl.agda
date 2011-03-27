
{-# OPTIONS --universe-polymorphism #-}

module Algorithm.Mergesort.Impl where

open import Logic
open import Function
open import Types
open import Data.Nat
open import Data.List
open import Relation.Equal
open import Relation.Equal.Nat
open import Relation.Order
open import Relation.Order.Nat

merge : ∀ {i}{A : Set i}{op : RelationOn A}{len : Nat} ->
        DecidableOrder op -> (xs ys : [ A ]) ->
        {eq : len == (length xs + length ys)} -> [ A ]
merge order [] ys = ys
merge {len = succ len} order (x :: xs) [] {eq} =
    x :: merge {len = len} order xs [] {==desucc eq}
merge {len = succ len} order (x :: xs) (y :: ys) {eq}
    with DecidableOrder.decide order x y
... | orLeft _ = x :: merge {len = len} order xs (y :: ys) {==desucc eq}
... | orRight _ = y :: merge {len = len} order (x :: xs) ys
    {==trans (==desucc eq) (==sym (addSuccReflexive {length xs}))}
merge {len = zero} _ (_ :: _) _ {()}

merge' : ∀ {i}{A : Set i}{op : RelationOn A} ->
         DecidableOrder op -> [ A ] -> [ A ] -> [ A ]
merge' order xs ys = merge {len = length xs + length ys} order xs ys {==refl}

mergePair : ∀ {i}{A : Set i}{op : RelationOn A} ->
            DecidableOrder op -> [ [ A ] ] -> [ [ A ] ]
mergePair order [] = []
mergePair order (x :: []) = x :: []
mergePair order (x :: x' :: xs) = merge' order x x' :: mergePair order xs

<=mergePair :
    ∀ {i}{A : Set i}{op : RelationOn A}{order : DecidableOrder op} ->
    (l : [ [ A ] ]) -> length (mergePair order l) <= length l
<=mergePair [] = <=zero
<=mergePair (_ :: []) = <=succ <=zero
<=mergePair (_ :: _ :: l) = <=succ $ <=trans (<=mergePair l) <=reflSucc

mergeAll :
    ∀ {i}{A : Set i}{op : RelationOn A}{n : Nat} ->
    DecidableOrder op -> (l : [ [ A ] ]) -> {rel : length l <= n} -> [ A ]
mergeAll order [] = []
mergeAll order (x :: []) = x
mergeAll {n = succ n} order (x :: x' :: xs) {<=succ rel} =
    mergeAll {n = n} order (mergePair order (x :: x' :: xs))
    {<=trans (<=succ (<=mergePair xs)) rel}
mergeAll {n = zero} _ (_ :: _) {()}

mergeAll' : ∀ {i}{A : Set i}{op : RelationOn A} ->
            DecidableOrder op -> [ [ A ] ] -> [ A ]
mergeAll' order xs = mergeAll {n = length xs} order xs {<=refl}

mergesort : ∀ {i}{A : Set i}{op : RelationOn A} ->
            DecidableOrder op -> [ A ] -> [ A ]
mergesort order xs = mergeAll' order $ map (flip _::_ []) xs
