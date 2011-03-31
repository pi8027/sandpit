
{-# OPTIONS --universe-polymorphism #-}

module Data.Bool where

data Bool : Set where
    false : Bool
    true : Bool

_&&_ : Bool → Bool → Bool
false && _ = false
true && b = b

_||_ : Bool → Bool  → Bool
false || b = b
true || _ = true

