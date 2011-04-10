
{-# OPTIONS --universe-polymorphism #-}

module RE.Core where

open import Level
open import Data.List
open import Data.List.All
open import Relation.Binary
open import Relation.Nullary

data ListEmpty {a} {A : Set a} : List A → Set a where
    listEmpty : ListEmpty []

data RE {a} (A : Set a) : Set a where
    reEmptySet : RE A            -- {}
    reEmptyString : RE A         -- {""}
    reSingleton : A → RE A       -- {character}
    reJoin : RE A → RE A → RE A  -- {xy | x ∈ L₁, y ∈ L₂}
    reUnion : RE A → RE A → RE A -- L₁ ∪ L₂
    reSequence : RE A → RE A     -- {""} ∪ {x | x ∈ L} ∪ {xx | x ∈ L} ∪ ...

data REMatch {a ℓ₁} {A : Set a} (_≈_ : Rel A ℓ₁) :
             REL (RE A) (List A) (a ⊔ ℓ₁) where
    reMatchEmptyString : REMatch _≈_ reEmptyString []
    reMatchSingleton : ∀ {c1 c2} → c1 ≈ c2 → REMatch _≈_ (reSingleton c1) [ c2 ]
    reMatchJoin : ∀ {re1 re2 s1 s2} → REMatch _≈_ re1 s1 → REMatch _≈_ re2 s2 →
                  REMatch _≈_ (reJoin re1 re2) (s1 ++ s2)
    reMatchUnionLeft : ∀ {re1 re2 str} →
                       REMatch _≈_ re1 str → REMatch _≈_ (reUnion re1 re2) str
    reMatchUnionRight : ∀ {re1 re2 str} →
                        REMatch _≈_ re2 str → REMatch _≈_ (reUnion re1 re2) str
    reMatchSequence :
        ∀ {re strList} →
        All (REMatch _≈_ re) strList → All (λ l → ¬ ListEmpty l) strList →
        REMatch _≈_ (reSequence re) (concat strList)

