
{-# OPTIONS --universe-polymorphism #-}

module Data.Nat where

import Level
open import Logic
open import Function
open import Data.Either
open import Relation.Binary.Core
open import Relation.Binary.Class
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
≡addSucc {succ n} = ≡apply₁ succ $ ≡addSucc {n}

-- Order Relation

data _≤_ : Rel Nat Level.zero where
    ≤0 : ∀ {n} → 0 ≤ n
    ≤succ : ∀ {m n} → m ≤ n → succ m ≤ succ n

≤unsucc : ∀ {m n} → succ m ≤ succ n → m ≤ n
≤unsucc (≤succ rel) = rel

≤refl : Reflexive _≤_
≤refl {0} = ≤0
≤refl {succ _} = ≤succ ≤refl

≤trans : Transitive _≤_
≤trans ≤0 p2 = ≤0
≤trans (≤succ p1) (≤succ p2) = ≤succ $ ≤trans p1 p2

≤antisym : Antisymmetric _≡_ _≤_
≤antisym ≤0 ≤0 = ≡refl
≤antisym (≤succ p1) (≤succ p2) = ≡apply₁ succ $ ≤antisym p1 p2

≤total : Total _≤_
≤total {a = 0} = left ≤0
≤total {b = 0} = right ≤0
≤total {succ a} {succ b} = eitherMap ≤succ ≤succ ≤total

≤decide : Decidable _≤_
≤decide 0 _ = left ≤0
≤decide (succ a) 0 = right \()
≤decide (succ a) (succ b) =
    eitherMap ≤succ (\ a≰b → a≰b ∘ ≤unsucc) (≤decide a b)
≤reflSucc : ∀ {i} → i ≤ succ i
≤reflSucc {0} = ≤0
≤reflSucc {succ _} = ≤succ ≤reflSucc

