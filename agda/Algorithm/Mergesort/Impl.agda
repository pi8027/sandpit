
{-# OPTIONS --universe-polymorphism #-}

module Algorithm.Mergesort.Impl where

open import Logic
open import Function
open import Data.Either
open import Data.Nat
open import Data.List
open import Relation.Binary.Core
open import Relation.Binary.Equal
open import Relation.Binary.Order

merge : ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} {len : Nat} →
        IsDecTotalOrder _≈_ _≲_ → (xs ys : List A) →
        {eq : len ≡ (length xs + length ys)} → List A
merge ord [] ys = ys
merge {len = succ len} ord (x ∷ xs) [] {eq} =
    x ∷ merge {len = len} ord xs [] {≡desucc eq}
merge {len = succ len} ord (x ∷ xs) (y ∷ ys) {eq}
    with IsDecTotalOrder.≤decide ord x y
... | left _ = x ∷ merge {len = len} ord xs (y ∷ ys) {≡desucc eq}
... | right _ = y ∷ merge {len = len} ord (x ∷ xs) ys
    {≡trans (≡desucc eq) (≡sym (≡addSucc {length xs}))}
merge {len = 0} _ (_ ∷ _) _ {()}

merge' : ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} →
         IsDecTotalOrder _≈_ _≲_ → List A → List A → List A
merge' ord xs ys = merge {len = length xs + length ys} ord xs ys {≡refl}

mergePair : ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} →
            IsDecTotalOrder _≈_ _≲_ → List (List A) → List (List A)
mergePair _ [] = []
mergePair _ (x ∷ []) = x ∷ []
mergePair ord (x ∷ x' ∷ xs) = merge' ord x x' ∷ mergePair ord xs

≤mergePair :
    ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} {order : IsDecTotalOrder _≈_ _≲_} →
    (l : List (List A)) → length (mergePair order l) ≤ length l
≤mergePair [] = ≤0
≤mergePair (_ ∷ []) = ≤succ ≤0
≤mergePair (_ ∷ _ ∷ l) = ≤succ $ ≤trans (≤mergePair l) ≤reflSucc

mergeAll :
    ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} {n : Nat} →
    IsDecTotalOrder _≈_ _≲_ → (l : List (List A)) → {rel : length l ≤ n} →
    List A
mergeAll _ [] = []
mergeAll _ (x ∷ []) = x
mergeAll {n = succ n} ord (x ∷ x' ∷ xs) {≤succ rel} =
    mergeAll {n = n} ord (mergePair ord (x ∷ x' ∷ xs))
    {≤trans (≤succ (≤mergePair xs)) rel}
mergeAll {n = 0} _ (_ ∷ _) {()}

mergeAll' : ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} →
            IsDecTotalOrder _≈_ _≲_ → List (List A) → List A
mergeAll' ord xs = mergeAll {n = length xs} ord xs {≤refl}

mergesort : ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} →
            IsDecTotalOrder _≈_ _≲_ → List A → List A
mergesort ord xs = mergeAll' ord $ map (flip _∷_ []) xs

