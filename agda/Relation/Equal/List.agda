
{-# OPTIONS --universe-polymorphism #-}

module Relation.Equal.List where

open import Level
open import Data.List
open import Relation.Equal

==head : ∀ {i}{A : Set i}{x y : A}{xs ys : [ A ]} ->
         (x :: xs) == (y :: ys) -> x == y
==head ==refl = ==refl

==tail : ∀ {i}{A : Set i}{x y : A}{xs ys : [ A ]} ->
         (x :: xs) == (y :: ys) -> xs == ys
==tail ==refl = ==refl

