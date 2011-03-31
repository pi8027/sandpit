
{-# OPTIONS --universe-polymorphism #-}

module Types where

open import Logic

BinOp : ∀ {a} → Set a → Set a
BinOp A = A → A → A

Decide : ∀ {a} → Set a → Set a
Decide P = P ∨ ¬ P