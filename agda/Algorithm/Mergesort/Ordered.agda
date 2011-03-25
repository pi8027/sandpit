
{-# OPTIONS --universe-polymorphism #-}

module Algorithm.Mergesort.Ordered where

open import Logic
open import Function
open import Types
open import Data.Nat
open import Data.List
open import Data.TList
open import Relation.Equal
open import Relation.Order
open import Relation.Order.Nat
open import Algorithm.Mergesort.Impl

merge-ordered :
    ∀ {i}{A : Set i}{op : RelationOn A}{b : A}{len : Nat} ->
    (order : DecidableOrder op) -> (xs ys : [ A ]) ->
    Ordered order b xs -> Ordered order b ys ->
    {eq : len == (length xs + length ys)} ->
    Ordered order b (merge order xs ys {eq})
merge-ordered _ [] _ _ p2 = p2
merge-ordered {len = succ _} order (x :: xs) [] (orderedCons .x p1 p2) _ =
    orderedCons x p1 $ merge-ordered order xs [] p2 orderedNull
merge-ordered {len = succ len} order (x :: xs) (y :: ys)
    (orderedCons .x p1 p2) (orderedCons .y p3 p4)
        with DecidableOrder.decide order x y
... | orLeft x<=y = orderedCons x p1 $
    merge-ordered {len = len} order xs (y :: ys) p2 (orderedCons y x<=y p4)
... | orRight !x<=y = orderedCons y p3 $
    merge-ordered {len = len} order (x :: xs) ys
        (orderedCons x (trichotomy' order !x<=y) p2) p4
merge-ordered {len = zero} _ (_ :: _) _ _ _ {()}

merge-ordered' :
    ∀ {i}{A : Set i}{op : RelationOn A}{b : A} ->
    (order : DecidableOrder op) -> (xs ys : [ A ]) ->
    Ordered order b xs -> Ordered order b ys ->
    Ordered order b (merge' order xs ys)
merge-ordered' order xs ys ox oy = merge-ordered order xs ys ox oy

mergePair-ordered :
    ∀ {i}{A : Set i}{op : RelationOn A}{b : A} ->
    (order : DecidableOrder op) -> (l : [ [ A ] ]) ->
    TList (map (Ordered order b) l) ->
    TList (map (Ordered order b) (mergePair order l))
mergePair-ordered order [] [*] = [*]
mergePair-ordered order (x :: []) (p :*: nullSeq) = p :*: nullSeq
mergePair-ordered order (x :: x' :: xs) (p :*: p' :*: p'') =
    merge-ordered' order x x' p p' :*: mergePair-ordered order xs p''

mergeAll-ordered :
    ∀ {i}{A : Set i}{op : RelationOn A}{b : A}{n : Nat} ->
    (order : DecidableOrder op) -> (l : [ [ A ] ]) ->
    {rel : length l <= n} -> TList (map (Ordered order b) l) ->
    Ordered order b (mergeAll order l {rel})
mergeAll-ordered order [] [*] = orderedNull
mergeAll-ordered order (x :: []) (p :*: _) = p
mergeAll-ordered {n = succ n} order (x :: x' :: xs) {<=succ rel} ordseq =
    mergeAll-ordered {n = n} order (mergePair order (x :: x' :: xs))
        (mergePair-ordered order (x :: x' :: xs) ordseq)
mergeAll-ordered {n = zero} _ (_ :: _) {()} _

mergeAll-ordered' :
    ∀ {i}{A : Set i}{op : RelationOn A}{b : A} ->
    (order : DecidableOrder op) -> (l : [ [ A ] ]) ->
    TList (map (Ordered order b) l) -> Ordered order b (mergeAll' order l)
mergeAll-ordered' order l ordseq =
    mergeAll-ordered {n = length l} order l {<=refl} ordseq

mergesort-ordered :
    ∀ {i}{A : Set i}{op : RelationOn A}{b : A} ->
    (order : DecidableOrder op) -> (l : [ A ]) ->
    TList (map (op b) l) -> Ordered order b (mergesort order l)
mergesort-ordered {A = A} {op} {b} order l ps =
    mergeAll-ordered' order (map (flip _::_ []) l) (p l ps) where
    p : (l : [ A ]) -> TList (map (op b) l) ->
        TList (map (Ordered order b) (map (flip _::_ []) l))
    p [] [*] = [*]
    p (x :: xs) (p1 :*: p2) = orderedCons x p1 orderedNull :*: p xs p2

