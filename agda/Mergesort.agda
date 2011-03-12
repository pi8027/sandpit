
{-# OPTIONS --termination-depth=2 #-}

module Mergesort where

open import Logic
open import Function
open import Relation
open import List
open import OList

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
-- merge order (x :: xs) (y :: ys) with DecidableOrder.decide order x y
-- ... | orLeft _  = x :: merge order xs (y :: ys)
-- ... | orRight _ = y :: merge order (x :: xs) ys

