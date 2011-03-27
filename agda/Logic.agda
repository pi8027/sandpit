
{-# OPTIONS --universe-polymorphism #-}

module Logic where

open import Level
open import Function

data ⊥ : Set where

⊥-elim : ∀ {a}{A : Set a} → ⊥ → A
⊥-elim ()

¬_ : ∀ {a} → Set a → Set a
¬ A = A → ⊥

data _∨_ {a : Level} (A B : Set a) : Set a where
    orLeft : A → A ∨ B
    orRight : B → A ∨ B

record _∧_ {a : Level} (A B : Set a) : Set a where
    field
        l : A
        r : B

orMerge : ∀ {a b}{A B : Set a}{C : Set b} →
          (A → C) → (B → C) → A ∨ B → C
orMerge f g (orLeft a) = f a
orMerge f g (orRight b) = g b

orMap : ∀ {a}{A B C D : Set a} →
        (A → C) → (B → D) → A ∨ B → C ∨ D
orMap f g = orMerge (orLeft ∘ f) (orRight ∘ g)

andLeft : ∀ {a}{A B : Set a} → A ∧ B → A
andLeft = _∧_.l

andRight : ∀ {a}{A B : Set a} → A ∧ B → B
andRight = _∧_.r

