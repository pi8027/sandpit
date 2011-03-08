
module Tuple where

data Tuple (A : Set) (B : Set) : Set where
    tuple : A -> B -> Tuple A B

