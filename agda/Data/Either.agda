
{-# OPTIONS --universe-polymorphism #-}

module Data.Either where

open import Level
open import Function

data Either {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
    left : A → Either A B
    right : B → Either A B

_∨_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
A ∨ B = Either A B

either : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
         (A → C) → (B → C) → Either A B → C
either f g (left a) = f a
either f g (right b) = g b

eitherMap : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
            (A → C) → (B → D) → Either A B → Either C D
eitherMap f g (left a) = left $ f a
eitherMap f g (right b) = right $ g b

