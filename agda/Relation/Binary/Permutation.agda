
{-# OPTIONS --universe-polymorphism #-}

module Relation.Binary.Permutation where

open import Function
open import Data.List
open import Relation.Binary.Core
open import Relation.Binary.Equal

data Permutation {i} {A : Set i} : Rel (List A) i where
    permNull : Permutation [] []
    permSkip : {h : A} {l l' : List A} →
               Permutation l l' → Permutation (h ∷ l) (h ∷ l')
    permSwap : {x x' : A} {xs : List A} →
               Permutation (x ∷ x' ∷ xs) (x' ∷ x ∷ xs)
    permTrans : {a b c : List A} →
                Permutation a b → Permutation b c → Permutation a c

eqPerm : ∀ {i} {A : Set i} {xs ys : List A} → xs ≡ ys → Permutation xs ys
eqPerm {xs = []} {[]} eq = permNull
eqPerm {xs = x ∷ xs} {y ∷ ys} eq =
    eqPerm' (≡head eq) (≡tail eq) where
    eqPerm' : ∀ {x y xs ys} →
              x ≡ y → xs ≡ ys → Permutation (x ∷ xs) (y ∷ ys)
    eqPerm' ≡refl eq = permSkip $ eqPerm eq
eqPerm {xs = []} {ys = _ ∷ _} ()
eqPerm {xs = _ ∷ _} {ys = []} ()


permAppendX : ∀ {i} {A : Set i} {xs xs' ys : List A} →
              Permutation xs xs' → Permutation (xs ++ ys) (xs' ++ ys)
permAppendX permNull = eqPerm ≡refl
permAppendX (permSkip p) = permSkip $ permAppendX p
permAppendX permSwap = permSwap
permAppendX (permTrans p1 p2) = permTrans (permAppendX p1) (permAppendX p2)

permAppendY : ∀ {i} {A : Set i} {xs ys ys' : List A} →
              Permutation ys ys' → Permutation (xs ++ ys) (xs ++ ys')
permAppendY {xs = []} p = p
permAppendY {xs = x ∷ xs} p = permSkip $ permAppendY {xs = xs} p

permAppend : ∀ {i} {A : Set i} {xs xs' ys ys' : List A} →
             Permutation xs xs' → Permutation ys ys' →
             Permutation (xs ++ ys) (xs' ++ ys')
permAppend {xs = xs} {xs'} p1 p2 =
    permTrans (permAppendX {xs = xs} p1) (permAppendY {xs = xs'} p2)

