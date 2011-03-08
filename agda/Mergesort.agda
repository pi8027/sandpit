
{-# OPTIONS --termination-depth=2 #-}

module Mergesort where

open import List

data Bool : Set where
    true : Bool
    false : Bool


record Unit : Set where


Compare : Set -> Set
Compare A = A -> A -> Bool


if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true then a else _ = a
if false then _ else a = a


merge : {A : Set} -> Compare A -> [ A ] -> [ A ] -> [ A ]
merge _ [] l = l
merge _ l [] = l
merge f (x :: xs) (y :: ys) =
    if (f x y) then (x :: merge f xs (y :: ys))
               else (y :: merge f (x :: xs) ys)



