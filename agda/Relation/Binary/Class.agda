
{-# OPTIONS --universe-polymorphism #-}

module Relation.Binary.Class where

open import Level
open import Logic
open import Function
open import Data.Either
open import Relation.Binary.Core

_⇒_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
      REL A B ℓ₁ → REL A B ℓ₂ → Set _
P ⇒ Q = ∀ {x y} → P x y → Q x y

Reflexive : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Reflexive _-_ = ∀ {x} → x - x

Irreflexive : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
              REL A B ℓ₁ → REL A B ℓ₂ → Set _
Irreflexive _≈_ _<_ = ∀ {x y} → x ≈ y → x < y

Sym : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
      REL A B ℓ₁ → REL B A ℓ₂ → Set _
Sym P Q = P ⇒ flip Q

Symmetric : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Symmetric _-_ = Sym _-_ _-_

Antisymmetric : ∀ {a ℓ₁ ℓ₂} {A : Set a} → Rel A ℓ₁ → Rel A ℓ₂ → Set _
Antisymmetric _≈_ _≤_ = ∀ {x y} → x ≤ y → y ≤ x → x ≈ y

Asym : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
       REL A B ℓ₁ → REL B A ℓ₂ → Set _
Asym _<₁_ _<₂_ = ∀ {x y} → x <₁ y → ¬ (y <₂ x)

Asymmetric : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Asymmetric _<_ = ∀ {x y} → x < y → ¬ (y < x)

Trans : ∀ {a b c ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : Set b} {C : Set c} →
        REL A B ℓ₁ → REL B C ℓ₂ → REL A C ℓ₃ → Set _
Trans P Q R = ∀ {x y z} → P x y → Q y z → R x z

FlipTrans : ∀ {a b c ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : Set b} {C : Set c} →
            REL A B ℓ₁ → REL B C ℓ₂ → REL A C ℓ₃ → Set _
FlipTrans P Q R = ∀ {x y z} → Q y z → P x y → R x z

Transitive : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Transitive _-_ = Trans _-_ _-_ _-_

Decidable : ∀ {a b ℓ} {A : Set a} {B : Set b} → REL A B ℓ → Set _
Decidable op = ∀ a b → op a b ∨ ¬ op a b

Total' : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
         REL A B ℓ₁ → REL B A ℓ₂ -> Set _
Total' P Q = ∀ {a b} → P a b ∨ Q b a

Total : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Total _-_ = Total' _-_ _-_

data Tri {a b c} (A : Set a) (B : Set b) (C : Set c) :
        Set (a ⊔ b ⊔ c) where
    tri< : A → ¬ B → ¬ C → Tri A B C
    tri≈ : ¬ A → B → ¬ C → Tri A B C
    tri> : ¬ A → ¬ B → C → Tri A B C

Trichotomous : ∀ {a ℓ₁ ℓ₂} {A : Set a} → Rel A ℓ₁ → Rel A ℓ₂ → Set _
Trichotomous _≈_ _<_ = ∀ {x y} → Tri (x < y) (x ≈ y) (y < x)

record IsEquivalence {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) :
                     Set (a ⊔ ℓ) where
    constructor isEquivalence
    field
        refl  : Reflexive _≈_
        sym   : Symmetric _≈_
        trans : Transitive _≈_

