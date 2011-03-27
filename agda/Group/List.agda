
{-# OPTIONS --universe-polymorphism #-}

module Group.List where

open import Function
open import Data.List
open import Relation.Equal
open import Group

++assoc : ∀ {i}{A : Set i}{a b c : [ A ]} ->
          (a ++ (b ++ c)) ≡ ((a ++ b) ++ c)
++assoc {a = []} = ≡refl
++assoc {a = x ∷ xs} = ≡apply'' _∷_ ≡refl $ ++assoc {a = xs}

++idleft : ∀ {i}{A : Set i}{a : [ A ]} -> ([] ++ a) ≡ a
++idleft = ≡refl

++idright : ∀ {i}{A : Set i}{a : [ A ]} -> (a ++ []) ≡ a
++idright {a = []} = ≡refl
++idright {a = x ∷ xs} = ≡apply'' _∷_ ≡refl ++idright

++Semigroup : ∀ {i}{A : Set i} -> Semigroup {A = [ A ]} _≡_ _++_
++Semigroup =
    record {
        base = ≡Equal;
        assoc = \{a} -> ++assoc {a = a}
    }

++Monoid : ∀ {i}{A : Set i} -> Monoid {A = [ A ]} _≡_ _++_ []
++Monoid =
    record {
        base = ++Semigroup;
        idleft = ++idleft;
        idright = ++idright
    }

