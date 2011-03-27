
{-# OPTIONS --universe-polymorphism #-}

module Relation.Permutation where

open import Level
open import Function
open import Types
open import Data.List
open import Relation.Equal
open import Relation.Equal.List

data Permutation {i : Level} {A : Set i} : RelationOn [ A ] where
    permNull : Permutation [] []
    permSkip : {h : A}{l l' : [ A ]} ->
               Permutation l l' -> Permutation (h ∷ l) (h ∷ l')
    permSwap : {x x' : A}{xs : [ A ]} ->
               Permutation (x ∷ x' ∷ xs) (x' ∷ x ∷ xs)
    permTrans : {a b c : [ A ]} ->
                Permutation a b -> Permutation b c -> Permutation a c

eqPerm : ∀ {i}{A : Set i}{xs ys : [ A ]} -> xs ≡ ys -> Permutation xs ys
eqPerm {xs = []} {[]} eq = permNull
eqPerm {xs = x ∷ xs} {y ∷ ys} eq =
    eqPerm' (≡head eq) (≡tail eq) where
    eqPerm' : ∀ {x y xs ys} ->
              x ≡ y -> xs ≡ ys -> Permutation (x ∷ xs) (y ∷ ys)
    eqPerm' ≡refl eq = permSkip $ eqPerm eq
eqPerm {xs = []} {ys = _ ∷ _} ()
eqPerm {xs = _ ∷ _} {ys = []} ()


permAppendX : ∀ {i}{A : Set i}{xs xs' ys : [ A ]} ->
              Permutation xs xs' -> Permutation (xs ++ ys) (xs' ++ ys)
permAppendX permNull = eqPerm ≡refl
permAppendX (permSkip p) = permSkip $ permAppendX p
permAppendX permSwap = permSwap
permAppendX (permTrans p1 p2) = permTrans (permAppendX p1) (permAppendX p2)

permAppendY : ∀ {i}{A : Set i}{xs ys ys' : [ A ]} ->
              Permutation ys ys' -> Permutation (xs ++ ys) (xs ++ ys')
permAppendY {xs = []} p = p
permAppendY {xs = x ∷ xs} p = permSkip $ permAppendY {xs = xs} p

permAppend : ∀ {i}{A : Set i}{xs xs' ys ys' : [ A ]} ->
             Permutation xs xs' -> Permutation ys ys' ->
             Permutation (xs ++ ys) (xs' ++ ys')
permAppend {xs = xs} {xs'} p1 p2 =
    permTrans (permAppendX {xs = xs} p1) (permAppendY {xs = xs'} p2)

