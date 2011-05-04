
{-# OPTIONS --universe-polymorphism #-}

module Data.Empty where

open import Level

data ⊥ : Set where

⊥-elim : ∀ {a} {A : Set a} → ⊥ → A
⊥-elim ()

