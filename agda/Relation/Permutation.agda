
module Relation.Permutation where

open import Logic
open import Function
open import Data.List
open import Relation

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

permAppendX : {A : Set}{xs xs' ys : [ A ]} ->
              Permutation xs xs' -> Permutation (xs ++ ys) (xs' ++ ys)
permAppendX permNull = permRefl
permAppendX (permSkip p) = permSkip $ permAppendX p
permAppendX permSwap = permSwap
permAppendX (permTrans p1 p2) = permTrans (permAppendX p1) (permAppendX p2)

permAppendY : {A : Set}{xs ys ys' : [ A ]} ->
              Permutation ys ys' -> Permutation (xs ++ ys) (xs ++ ys')
permAppendY {xs = []} p = p
permAppendY {xs = x :: xs} p = permSkip $ permAppendY {xs = xs} p

permAppend : {A : Set}{xs xs' ys ys' : [ A ]} ->
             Permutation xs xs' -> Permutation ys ys' ->
             Permutation (xs ++ ys) (xs' ++ ys')
permAppend {xs' = xs'} p1 p2 =
    permTrans (permAppendX p1) (permAppendY {xs = xs'} p2)

permAppend' : {A : Set}{xs ys zs : [ A ]} ->
              Permutation ((xs ++ ys) ++ zs) (xs ++ (ys ++ zs))
permAppend' {xs = []} {ys} {zs} = permAppend {xs = ys} permRefl permRefl
permAppend' {xs = x :: xs} {ys} {zs} = permSkip $ permAppend' {xs = xs}
