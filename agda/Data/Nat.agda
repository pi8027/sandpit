
{-# OPTIONS --universe-polymorphism #-}

module Data.Nat where

import Level
open import Logic
open import Types
open import Function
open import Relation.Binary.Core
open import Relation.Binary.Equal
open import Relation.Binary.Order

data Nat : Set where
    zero : Nat
    succ : Nat → Nat

{-# BUILTIN NATURAL Nat  #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     succ #-}

-- Nat Operation

_+_ : Nat → Nat → Nat
0 + b = b
succ a + b = succ (a + b)

_*_ : Nat → Nat → Nat
0 * b = 0
succ a * b = b + (a * b)

desucc : {n : Nat} → (m : Nat) → {eq : succ n ≡ m} → Nat
desucc (succ m) = m
desucc 0 {()}

-- Equality Relation

≡desucc : {n m : Nat} → (succ n ≡ succ m) → (n ≡ m)
≡desucc ≡refl = ≡refl

≡addSucc : {n m : Nat} → (succ n + m) ≡ (n + succ m)
≡addSucc {0} = ≡refl
≡addSucc {succ n} = ≡apply' succ $ ≡addSucc {n}

-- Order Relation

data _≤_ : Rel Nat Level.zero where
    ≤0 : ∀ {n} → 0 ≤ n
    ≤succ : ∀ {m n} → m ≤ n → succ m ≤ succ n

≤unsucc : ∀ {m n} → succ m ≤ succ n → m ≤ n
≤unsucc (≤succ rel) = rel

≤refl : ∀ {i} → i ≤ i
≤refl {0} = ≤0
≤refl {succ _} = ≤succ ≤refl

≤trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
≤trans ≤0 p2 = ≤0
≤trans (≤succ p1) (≤succ p2) = ≤succ $ ≤trans p1 p2

≤total : ∀ {a b} → (a ≤ b) ∨ (b ≤ a)
≤total {a = 0} = ≤0 ∨-
≤total {b = 0} = -∨ ≤0
≤total {succ a} {succ b} = orMap ≤succ ≤succ ≤total

≤decide : (a b : Nat) → Decide (a ≤ b)
≤decide 0 _ = ≤0 ∨-
≤decide (succ a) 0 = -∨ \()
≤decide (succ a) (succ b) = orMap ≤succ (\ a≰b → a≰b ∘ ≤unsucc) (≤decide a b)

≤Order : Order _≤_
≤Order = order ≤refl ≤trans

≤TotalOrder : TotalOrder _≤_
≤TotalOrder = torder ≤Order ≤total

≤DecidableOrder : DecidableOrder _≤_
≤DecidableOrder = dorder ≤TotalOrder ≤decide

≤reflSucc : ∀ {i} → i ≤ succ i
≤reflSucc {0} = ≤0
≤reflSucc {succ _} = ≤succ ≤reflSucc
