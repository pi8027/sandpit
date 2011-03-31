
{-# OPTIONS --universe-polymorphism #-}

module Relation.Binary.Equal where

open import Level
open import Function
open import Relation.Binary.Core

data _≡_ {i} {A : Set i} : Rel A i where
    ≡refl : {a : A} → a ≡ a

record Equal {i} {A : Set i} (eq : Rel A i) : Set i where
    field
        refl : ∀ {a : A} → eq a a
        sym : ∀ {a b : A} → eq b a → eq a b
        trans : ∀ {a b c : A} → eq a b → eq b c → eq a c

≡sym : ∀ {i} {A : Set i} {a b : A} → b ≡ a → a ≡ b
≡sym ≡refl = ≡refl

≡trans : ∀ {i} {A : Set i} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
≡trans ≡refl ≡refl = ≡refl

≡apply' : ∀ {i j} {A : Set i} {B : Set j} {a a' : A} →
           (f : A → B) → a ≡ a' → f a ≡ f a'
≡apply' f ≡refl = ≡refl

≡apply'' : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} {a a' : A} {b b' : B} →
            (f : A → B → C) → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
≡apply'' f ≡refl ≡refl = ≡refl

≡Equal : ∀ {a} {A : Set a} → Equal {a} {A} _≡_
≡Equal {A} = record { refl = ≡refl; sym = ≡sym; trans = ≡trans}

