
module Data.Nat where

open import Function

data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero + b = b
succ a + b = succ $ a + b

