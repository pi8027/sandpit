
{-# OPTIONS --universe-polymorphism #-}

module Algorithm.Mergesort.Impl where

open import Logic
open import Function
open import Data.Either
open import Data.Nat
open import Data.List
open import Relation.Binary.Core
open import Relation.Binary.Class
open import Relation.Binary.Equal
open import Relation.Binary.Order

deccase : ∀ {i j} {A : Set i} {B : Set j} {_∼_ : Rel A i} →
          (x y : A) → Decidable _∼_ → (x ∼ y → B) → (¬ (x ∼ y) → B) → B
deccase x y dec f g with dec x y
... | left x∼y = f x∼y
... | right ¬x∼y = g ¬x∼y

deccaseP :
    ∀ {i j p} {A : Set i} {B : Set j} {_∼_ : Rel A i} →
    (P : B → Set p) → (x y : A) → (dec : Decidable _∼_) →
    (f : x ∼ y → B) → (g : ¬ (x ∼ y) → B) →
    ((r : x ∼ y) → P (f r)) → ((r : ¬ (x ∼ y)) → P (g r)) →
    P (deccase x y dec f g)
deccaseP P x y dec f g fp gp with dec x y
... | left x∼y = fp x∼y
... | right ¬x∼y = gp ¬x∼y

merge : ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} →
        IsDecTotalOrder _≈_ _≲_ → List A → List A → List A
merge ord [] ys = ys
merge ord xs [] = xs
merge ord (x ∷ xs) (y ∷ ys) = deccase x y (IsDecTotalOrder.≤decide ord)
    (λ _ → x ∷ merge ord xs (y ∷ ys))
    (λ _ → y ∷ merge ord (x ∷ xs) ys)

mergePair : ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} →
            IsDecTotalOrder _≈_ _≲_ → List (List A) → List (List A)
mergePair _ [] = []
mergePair _ (x ∷ []) = x ∷ []
mergePair ord (x ∷ x' ∷ xs) = merge ord x x' ∷ mergePair ord xs

≤mergePair :
    ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} {order : IsDecTotalOrder _≈_ _≲_} →
    (l : List (List A)) → length (mergePair order l) ≤ length l
≤mergePair [] = ≤0
≤mergePair (_ ∷ []) = ≤succ ≤0
≤mergePair (_ ∷ _ ∷ l) = ≤succ $ ≤trans (≤mergePair l) ≤reflSucc

mergeAll : ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} {n : Nat} →
           IsDecTotalOrder _≈_ _≲_ →
           (l : List (List A)) → length l ≤ n → List A
mergeAll _ [] _ = []
mergeAll _ (x ∷ []) _ = x
mergeAll ord (x ∷ x' ∷ xs) (≤succ rel) =
    mergeAll ord (mergePair ord (x ∷ x' ∷ xs))
        (≤trans (≤succ (≤mergePair xs)) rel)

mergeAll' : ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} →
            IsDecTotalOrder _≈_ _≲_ → List (List A) → List A
mergeAll' ord xs = mergeAll ord xs ≤refl

mergesort : ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} →
            IsDecTotalOrder _≈_ _≲_ → List A → List A
mergesort ord xs = mergeAll' ord $ map (flip _∷_ []) xs

