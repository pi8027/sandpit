
{-# OPTIONS --universe-polymorphism #-}

module Algorithm.Mergesort.Permutation where

open import Logic
open import Function
open import Data.Either
open import Data.Nat
open import Data.List
open import Group.List
open import Relation.Binary.Core
open import Relation.Binary.Equal
open import Relation.Binary.Order
open import Relation.Binary.Permutation
open import Algorithm.Mergesort.Impl

merge-permutation :
    ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} {len : Nat} →
    (order : IsDecTotalOrder _≈_ _≲_) → (xs ys : List A) →
    {eq : len ≡ (length xs + length ys)} →
    Permutation (xs ++ ys) (merge order xs ys {eq})
merge-permutation ord [] ys = eqPerm ≡refl
merge-permutation {len = succ len} ord (x ∷ xs) [] =
    permSkip $ merge-permutation ord xs []
merge-permutation {A = A} {len = succ len} ord (x ∷ xs) (y ∷ ys)
    with IsDecTotalOrder.≤decide ord x y
... | left _ = permSkip $ merge-permutation {len = len} ord xs (y ∷ ys)
... | right _ = permTrans (move {xs = x ∷ xs}) $ permSkip $
    merge-permutation {len = len} ord (x ∷ xs) ys where
    move : {y : A} {xs ys : List A} →
           Permutation (xs ++ (y ∷ ys)) (y ∷ xs ++ ys)
    move {xs = []} = eqPerm ≡refl
    move {xs = x ∷ xs} = permTrans (permSkip (move {xs = xs})) permSwap
merge-permutation {len = 0} _ (_ ∷ _) _ {()}

merge-permutation' :
    ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} →
    (order : IsDecTotalOrder _≈_ _≲_) → (xs ys : List A) →
    Permutation (xs ++ ys) (merge' order xs ys)
merge-permutation' ord xs ys = merge-permutation ord xs ys

mergePair-permutation :
    ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} →
    (order : IsDecTotalOrder _≈_ _≲_) → (l : List (List A)) →
    Permutation (concat l) (concat (mergePair order l))
mergePair-permutation _ [] = permNull
mergePair-permutation _ (x ∷ []) = eqPerm ≡refl
mergePair-permutation ord (x ∷ x' ∷ xs) =
    permTrans (eqPerm (++assoc {a = x}))
    (permAppend (merge-permutation ord x x') (mergePair-permutation ord xs))

mergeAll-permutation :
    ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} {n : Nat} →
    (order : IsDecTotalOrder _≈_ _≲_) → (l : List (List A)) →
    {rel : length l ≤ n} → Permutation (concat l) (mergeAll order l {rel})
mergeAll-permutation _ [] = permNull
mergeAll-permutation _ (x ∷ []) = eqPerm ++idright
mergeAll-permutation {n = succ n} ord (x ∷ x' ∷ xs) {≤succ rel} =
    permTrans (mergePair-permutation ord (x ∷ x' ∷ xs))
        (mergeAll-permutation {n = n} ord (mergePair ord (x ∷ x' ∷ xs)))
mergeAll-permutation {n = 0} _ (_ ∷ _) {()}

mergeAll-permutation' :
    ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} →
    (order : IsDecTotalOrder _≈_ _≲_) → (l : List (List A)) →
    Permutation (concat l) (mergeAll' order l)
mergeAll-permutation' ord l = mergeAll-permutation {n = length l} ord l

mergesort-permutation :
    ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} →
    (order : IsDecTotalOrder _≈_ _≲_) → (l : List A) →
    Permutation l (mergesort order l)
mergesort-permutation ord l =
    permTrans (eqPerm p) (mergeAll-permutation' ord (map (flip _∷_ []) l))
    where
    p : ∀ {l} → l ≡ concat (map (flip _∷_ []) l)
    p {[]} = ≡refl
    p {x ∷ xs} = ≡apply₁ (_∷_ x) $ p {xs}

