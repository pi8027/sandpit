
{-# OPTIONS --universe-polymorphism #-}

module Algorithm.Mergesort.Ordered where

open import Function
open import Data.Either
open import Data.Empty
open import Data.Nat
open import Data.List
open import Data.TList
open import Relation.Binary.Core
open import Relation.Binary.Equal
open import Relation.Binary.Order
open import Relation.Binary.Class
open import Algorithm.Mergesort.Impl

merge-ordered :
    ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} {b : A} →
    (len : Nat) → (order : IsDecTotalOrder _≈_ _≲_) → (xs ys : List A) →
    Ordered _≲_ b xs → Ordered _≲_ b ys →
    {eq : len ≡ (length xs + length ys)} →
    Ordered _≲_ b (merge order xs ys {eq})
merge-ordered _ _ [] _ _ p2 = p2
merge-ordered (succ len) ord (x ∷ xs) [] (orderedCons .x p1 p2) _ =
    orderedCons x p1 $ merge-ordered len ord xs [] p2 orderedNull
merge-ordered (succ len) ord
    (x ∷ xs) (y ∷ ys) (orderedCons .x p1 p2) (orderedCons .y p3 p4)
        with IsDecTotalOrder.≤decide ord x y |
             IsTotalOrder.total (IsDecTotalOrder.totalorder ord) {x} {y}
... | left x≤y | _ = orderedCons x p1 $
        merge-ordered len ord xs (y ∷ ys) p2 (orderedCons y x≤y p4)
... | right x≰y | left x≤y = ⊥-elim $ x≰y x≤y
... | right x≰y | right y≤x = orderedCons y p3 $
        merge-ordered len ord (x ∷ xs) ys (orderedCons x y≤x p2) p4
merge-ordered 0 _ (_ ∷ _) _ _ _ {()}

merge-ordered' :
    ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} {b : A} →
    (order : IsDecTotalOrder _≈_ _≲_) → (xs ys : List A) →
    Ordered _≲_ b xs → Ordered _≲_ b ys →
    Ordered _≲_ b (merge' order xs ys)
merge-ordered' ord xs ys ox oy =
    merge-ordered (length xs + length ys) ord xs ys ox oy

mergePair-ordered :
    ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} {b : A} →
    (order : IsDecTotalOrder _≈_ _≲_) → (l : List (List A)) →
    All (Ordered _≲_ b) l → All (Ordered _≲_ b) (mergePair order l)
mergePair-ordered _ [] [] = []
mergePair-ordered _ (x ∷ []) (p ∷ nullSeq) = p ∷ nullSeq
mergePair-ordered ord (x ∷ x' ∷ xs) (p ∷ p' ∷ p'') =
    merge-ordered' ord x x' p p' ∷ mergePair-ordered ord xs p''

mergeAll-ordered :
    ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} {b : A} {n : Nat} →
    (order : IsDecTotalOrder _≈_ _≲_) → (l : List (List A)) →
    {rel : length l ≤ n} → All (Ordered _≲_ b) l →
    Ordered _≲_ b (mergeAll order l {rel})
mergeAll-ordered _ [] [*] = orderedNull
mergeAll-ordered ord (x ∷ []) (p ∷ _) = p
mergeAll-ordered {n = succ n} ord (x ∷ x' ∷ xs) {≤succ rel} ordseq =
    mergeAll-ordered {n = n} ord (mergePair ord (x ∷ x' ∷ xs))
        (mergePair-ordered ord (x ∷ x' ∷ xs) ordseq)
mergeAll-ordered {n = 0} _ (_ ∷ _) {()} _

mergeAll-ordered' :
    ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} {b : A} →
    (order : IsDecTotalOrder _≈_ _≲_) → (l : List (List A)) →
    All (Ordered _≲_ b) l → Ordered _≲_ b (mergeAll' order l)
mergeAll-ordered' ord l ordseq =
    mergeAll-ordered {n = length l} ord l {≤refl} ordseq

mergesort-ordered :
    ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} {b : A} →
    (order : IsDecTotalOrder _≈_ _≲_) → (l : List A) →
    All (_≲_ b) l → Ordered _≲_ b (mergesort order l)
mergesort-ordered {A = A} {_≈_} {_≲_} {b} ord l ps =
    mergeAll-ordered' ord (map (λ a → a ∷ []) l) (p l ps) where
    p : (l : List A) → All (_≲_ b) l →
        All (Ordered _≲_ b) (map (λ a → a ∷ []) l)
    p [] [] = []
    p (x ∷ xs) (p1 ∷ p2) = orderedCons x p1 orderedNull ∷ p xs p2

