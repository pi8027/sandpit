
module List where

open import Nat

infixr 40 _::_

data List (A : Set) : Set where
    []   : List A
    _::_ : A -> List A -> List A

