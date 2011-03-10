
{-# OPTIONS --termination-depth=2 #-}

module Mergesort where

open import Logic
open import Function
open import Relation
open import List

-- caseord : {A B : Set}{op : Relation A A} ->
--     ((x y : A) -> Order op x y) -> (x y : A) ->
--     (op x y -> B) -> ((op x y -> False) -> B) -> B
-- caseord ord x y f g with ord x y
-- ... | leq a = f a
-- ... | gt a  = g a

-- merge : {A : Set}{op : Relation A A} ->
--     ((x y : A) -> Order op x y) -> OrderLaws op ->
--     [ A ] -> [ A ] -> [ A ]
-- merge _ _ [] l = l
-- merge _ _ l [] = l
-- merge ord laws (x :: xs) (y :: ys) =
--     caseord ord x y
--         (const (x :: merge ord laws xs (y :: ys)))
--         (const (y :: merge ord laws (x :: xs) ys))

-- merge ord laws (x :: xs) (y :: ys) with ord x y
-- ... | leq _ = x :: merge ord laws xs (y :: ys)
-- ... | gt _  = y :: merge ord laws (x :: xs) ys

