
{-# OPTIONS --universe-polymorphism #-}

module Relation.Equal.Nat where

open import Level
open import Function
open import Data.Nat
open import Relation.Equal

==desucc : {n m : Nat} -> succ n == succ m -> n == m
==desucc ==refl = ==refl

addSuccReflexive : {n m : Nat} -> (succ n + m) == (n + succ m)
addSuccReflexive {zero} = ==refl
addSuccReflexive {succ n} = ==apply' succ $ addSuccReflexive {n}

==+ : {n n' m m' : Nat} -> n == n' -> m == m' -> (n + m) == (n' + m')
==+ ==refl ==refl = ==refl
