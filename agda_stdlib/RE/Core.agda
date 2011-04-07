
{-# OPTIONS --universe-polymorphism #-}

module RE.Core where

open import Level
open import Function
open import Data.Empty
open import Data.List
open import Data.List.All
open import Relation.Binary
open import Relation.Nullary

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
    reMatchSequence : ∀ {re strList} → All (REMatch _≈_ re) strList →
                      REMatch _≈_ (reSequence re) (concat strList)

match : ∀ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ} → Decidable _≈_ → Decidable (REMatch _≈_)
match _ reEmptySet _ = no (λ ())
match _ reEmptyString [] = yes reMatchEmptyString
match _ reEmptyString (c ∷ cs) = no (λ ())
match dec (reSingleton _) [] = no (λ ())
match {_≈_ = _≈_} dec (reSingleton c1) (c2 ∷ []) with dec c1 c2
... | yes c1≈c2 = yes $ reMatchSingleton c1≈c2
... | no ¬c1≈c2 = no f where
    f : ¬ REMatch _≈_ (reSingleton c1) (c2 ∷ [])
    f (reMatchSingleton c1≈c2) = ⊥-elim $ ¬c1≈c2 c1≈c2
match dec (reSingleton _) (_ ∷ _ ∷ _) = no (λ ())
match dec (reJoin re1 re2) str = {!!}
match {_≈_ = _≈_} dec (reUnion re1 re2) str
        with match dec re1 str | match dec re2 str
... | yes p | _ = yes $ reMatchUnionLeft p
... | no _ | yes p = yes $ reMatchUnionRight p
... | no p1 | no p2 = no f where
    f : ¬ REMatch _≈_ (reUnion re1 re2) str
    f (reMatchUnionLeft ¬p1) = ⊥-elim $ p1 ¬p1
    f (reMatchUnionRight ¬p2) = ⊥-elim $ p2 ¬p2
match dec (reSequence re) str = {!!}
