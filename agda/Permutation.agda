
module Permutation where

open import Logic
open import Function
open import Relation
open import List

data Permutation {A : Set} : RelationOn [ A ] where
    permNull : Permutation [] []
    permSkip : {h : A}{l l' : [ A ]} ->
               Permutation l l' -> Permutation (h :: l) (h :: l')
    permSwap : {x x' : A}{xs : [ A ]} ->
               Permutation (x :: x' :: xs) (x' :: x :: xs)
    permTrans : {a b c : [ A ]} ->
                Permutation a b -> Permutation b c -> Permutation a c

permRefl : {A : Set}{l : [ A ]} -> Permutation l l
permRefl {l = []} = permNull
permRefl {l = _ :: _} = permSkip permRefl

permSym : {A : Set}{l1 l2 : [ A ]} -> Permutation l1 l2 -> Permutation l2 l1
permSym permNull = permNull
permSym (permSkip perm) = permSkip $ permSym perm
permSym permSwap = permSwap
permSym (permTrans perm1 perm2) = permTrans (permSym perm2) (permSym perm1)

