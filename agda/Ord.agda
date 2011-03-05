
module Ord where

open import Bool

record OrderRelation (A : Set) : Set where
    field f     : A -> A -> Bool
          refl  : (a : A) -> isTrue (f a a)
          trans : (a b c : A) ->
                      isTrue (f a b) -> isTrue (f b c) -> isTrue (f a c)

