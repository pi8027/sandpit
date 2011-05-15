
{-# OPTIONS --universe-polymorphism #-}

module Relation.Binary.Equal where

open import Relation.Binary.Core
open import Relation.Binary.Class

data _≡_ {i} {A : Set i} : Rel A i where
    ≡refl : {a : A} → a ≡ a

≡sym : ∀ {a} {A : Set a} → Symmetric {A = A} _≡_
≡sym ≡refl = ≡refl

≡trans : ∀ {a} {A : Set a} → Transitive {A = A} _≡_
≡trans ≡refl ≡refl = ≡refl

≡apply₁ : ∀ {i j} {A : Set i} {B : Set j} {a a' : A} →
           (f : A → B) → a ≡ a' → f a ≡ f a'
≡apply₁ f ≡refl = ≡refl

≡apply₂ : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} {a a' : A} {b b' : B} →
            (f : A → B → C) → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
≡apply₂ f ≡refl ≡refl = ≡refl

≡typing : ∀ {t} {T1 T2 : Set t} → T1 ≡ T2 → T1 → T2
≡typing ≡refl a = a

≡Equal : ∀ {a} {A : Set a} → IsEquivalence (_≡_ {a} {A})
≡Equal = isEquivalence ≡refl ≡sym ≡trans


