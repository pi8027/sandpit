
{-# OPTIONS --universe-polymorphism #-}

module Algorithm.Mergesort.Ordered where

open import Function
open import Data.Nat
open import Data.List
open import Data.TList
open import Relation.Binary.Core
open import Relation.Binary.Order
open import Algorithm.Mergesort.Impl

merge-ordered :
    ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} {b : A} →
    (order : IsDecTotalOrder _≈_ _≲_) → (xs ys : List A) →
    Ordered _≲_ b xs → Ordered _≲_ b ys →
    Ordered _≲_ b (merge order xs ys)
merge-ordered ord [] ys orderedNull oy = oy
merge-ordered ord (_ ∷ _) [] ox orderedNull = ox
merge-ordered {_≲_ = _≲_} {b}
    ord (x ∷ xs) (y ∷ ys) (orderedCons .x p1 p2) (orderedCons .y p3 p4) =
    deccaseP (Ordered _≲_ b) x y (IsDecTotalOrder.≤decide ord)
        (λ x≲y → x ∷ merge ord xs (y ∷ ys))
        (λ ¬x≲y → y ∷ merge ord (x ∷ xs) ys)
        (λ x≲y → orderedCons x p1
            (merge-ordered ord xs (y ∷ ys) p2 (orderedCons y x≲y p4)))
        (λ ¬x≲y → orderedCons y p3 (merge-ordered ord (x ∷ xs) ys
            (orderedCons x (IsDecTotalOrder.total' ord ¬x≲y) p2) p4))

mergePair-ordered :
    ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} {b : A} →
    (order : IsDecTotalOrder _≈_ _≲_) → (l : List (List A)) →
    All (Ordered _≲_ b) l → All (Ordered _≲_ b) (mergePair order l)
mergePair-ordered _ [] [] = []
mergePair-ordered _ (x ∷ []) (p ∷ nullSeq) = p ∷ nullSeq
mergePair-ordered ord (x ∷ x' ∷ xs) (p ∷ p' ∷ p'') =
    merge-ordered ord x x' p p' ∷ mergePair-ordered ord xs p''

mergeAll-ordered :
    ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} {b : A} {n : Nat} →
    (order : IsDecTotalOrder _≈_ _≲_) → (l : List (List A)) →
    {rel : length l ≤ n} → All (Ordered _≲_ b) l →
    Ordered _≲_ b (mergeAll order l rel)
mergeAll-ordered _ [] [] = orderedNull
mergeAll-ordered ord (x ∷ []) (p ∷ _) = p
mergeAll-ordered ord (x ∷ x' ∷ xs) {≤succ _} ordseq =
    mergeAll-ordered ord (mergePair ord (x ∷ x' ∷ xs))
        (mergePair-ordered ord (x ∷ x' ∷ xs) ordseq)

mergesort-ordered :
    ∀ {i} {A : Set i} {_≈_ _≲_ : Rel A i} {b : A} →
    (order : IsDecTotalOrder _≈_ _≲_) → (l : List A) →
    All (_≲_ b) l → Ordered _≲_ b (mergesort order l)
mergesort-ordered {A = A} {_≈_} {_≲_} {b} ord l ps =
    mergeAll-ordered ord (map (flip′ _∷_ []) l)
        (mapAll l (λ {x} p → orderedCons x p orderedNull) ps)

