
module Relation.Equal.List where

open import Data.List
open import Relation
open import Relation.Equal

==cons : ∀ {A}{x y : A}{xs ys : [ A ]} ->
         x == y -> xs == ys -> (x :: xs) == (y :: ys)
==cons ==refl ==refl = ==refl

==head : ∀ {A}{x y : A}{xs ys : [ A ]} ->
         (x :: xs) == (y :: ys) -> x == y
==head ==refl = ==refl

==tail : ∀ {A}{x y : A}{xs ys : [ A ]} ->
         (x :: xs) == (y :: ys) -> xs == ys
==tail ==refl = ==refl

