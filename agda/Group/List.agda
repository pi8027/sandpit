
{-# OPTIONS --universe-polymorphism #-}

module Group.List where

open import Function
open import Data.List
open import Relation.Binary.Equal
open import Group

++assoc : ∀ {i} {A : Set i} {a b c : List A} →
          (a ++ (b ++ c)) ≡ ((a ++ b) ++ c)
++assoc {a = []} = ≡refl
++assoc {a = x ∷ xs} = ≡apply'' _∷_ ≡refl $ ++assoc {a = xs}

++idleft : ∀ {i} {A : Set i} {a : List A} → ([] ++ a) ≡ a
++idleft = ≡refl

++idright : ∀ {i} {A : Set i} {a : List A} → (a ++ []) ≡ a
++idright {a = []} = ≡refl
++idright {a = x ∷ xs} = ≡apply'' _∷_ ≡refl ++idright

++Semigroup : ∀ {i} {A : Set i} → Semigroup {A = List A} _≡_ _++_
++Semigroup = semigroup ≡Equal (\{a} → ++assoc {a = a})

++Monoid : ∀ {i} {A : Set i} → Monoid {A = List A} _≡_ _++_ []
++Monoid = monoid ++Semigroup ++idleft ++idright

