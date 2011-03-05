
module List where

open import Nat

infixr 40 _::_

data List (A : Set) : Set where
    []   : List A
    _::_ : A -> List A -> List A

length : forall { A } -> List A -> Nat
length [] = zero
length (x :: xs) = succ (length xs)

