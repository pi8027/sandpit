
{-# OPTIONS --universe-polymorphism #-}

module Relation.Binary.Class where

open import Level
open import Logic
open import Function
open import Relation.Binary.Core

_⇒_ : ∀ {i j k l} {A : Set i} {B : Set j} →
      REL A B k → REL A B l → Set (i ⊔ j ⊔ k ⊔ l)
P ⇒ Q = ∀ {x y} → P x y → Q x y

Reflexive : ∀ {i j} {A : Set i} → Rel A j → Set (i ⊔ j)
Reflexive _-_ = ∀ {x} → x - x

Irreflexive : ∀ {i j k l} {A : Set i} {B : Set j} →
              REL A B k → REL A B l → Set (i ⊔ j ⊔ k ⊔ l)
Irreflexive _≈_ _<_ = ∀ {x y} → x ≈ y → x < y

Sym : ∀ {i j k l} {A : Set i} {B : Set j} →
      REL A B k → REL B A l → Set (i ⊔ j ⊔ k ⊔ l)
Sym P Q = P ⇒ flip Q

Symmetric : ∀ {i j} {A : Set i} → Rel A j → Set (i ⊔ j)
Symmetric _-_ = Sym _-_ _-_


