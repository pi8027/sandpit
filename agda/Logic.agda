
{-# OPTIONS --universe-polymorphism #-}

module Logic where

open import Data.Empty

¬_ : ∀ {a} → Set a → Set a
¬ A = A → ⊥

record _∧_ {a} (A B : Set a) : Set a where
    field
        l : A
        r : B

andLeft : ∀ {a} {A B : Set a} → A ∧ B → A
andLeft = _∧_.l

andRight : ∀ {a} {A B : Set a} → A ∧ B → B
andRight = _∧_.r

