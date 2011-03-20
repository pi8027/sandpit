
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

permFalse : {A : Set}{h : A}{t : [ A ]} -> Permutation [] (h :: t) -> False
permFalse (permTrans {b = b} p1 p2) with b
... | _ :: _ = permFalse p1
... | [] = permFalse p2

permAppendNull : {A : Set}{l : [ A ]} -> Permutation (l ++ []) l
permAppendNull {l = []} = permNull
permAppendNull {l = x :: xs} = permSkip $ permAppendNull

permSkipMany : {A : Set}{l1 l2 l3 : [ A ]} ->
               Permutation l2 l3 -> Permutation (l1 ++ l2) (l1 ++ l3)
permSkipMany {l1 = []} perm = perm
permSkipMany {l1 = x :: xs} perm = permSkip $ permSkipMany {l1 = xs} perm

permSkipMany' : {A : Set}{l1 l2 l3 : [ A ]} ->
                Permutation l1 l2 -> Permutation (l1 ++ l3) (l2 ++ l3)
permSkipMany' permNull = permSkipMany {l1 = []} permRefl
permSkipMany' (permSkip perm) = permSkip $ permSkipMany' perm
permSkipMany' permSwap = permSwap
permSkipMany' (permTrans perm1 perm2) =
    permTrans (permSkipMany' perm1) (permSkipMany' perm2)

permAppend : {A : Set}{l1 l2 l3 l4 : [ A ]} ->
             Permutation l1 l2 -> Permutation l3 l4 -> Permutation (l1 ++ l3) (l2 ++ l4)
permAppend permNull perm = perm
permAppend (permSkip perm1) perm2 = permSkip (permAppend perm1 perm2)
permAppend {l1 = _ :: _ :: xs} permSwap perm =
    permTrans permSwap $ permSkip $ permSkip $ permSkipMany {l1 = xs} perm
permAppend (permTrans perm1 perm2) perm3 =
    permTrans (permSkipMany' perm1) (permAppend perm2 perm3)

