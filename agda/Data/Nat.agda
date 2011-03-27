
{-# OPTIONS --universe-polymorphism #-}

module Data.Nat where

open import Function
open import Relation.Equal

data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero + b = b
succ a + b = succ $ a + b

_*_ : Nat -> Nat -> Nat
zero * b = zero
succ a * b = b + (a * b)

desucc : {n : Nat} -> (m : Nat) -> {eq : succ n == m} -> Nat
desucc (succ m) = m
desucc zero {()}