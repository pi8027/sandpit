
{-# OPTIONS --universe-polymorphism #-}

module Algorithm.Mergesort.Ordered where

open import Logic
open import Function
open import Data.Nat
open import Data.List
open import Data.TList
open import Relation.Binary.Core
open import Relation.Binary.Equal
open import Relation.Binary.Order
open import Algorithm.Mergesort.Impl

merge-ordered :
    ∀ {i} {A : Set i} {op : Rel A i} {b : A} {len : Nat} →
    (order : DecidableOrder op) → (xs ys : List A) →
    Ordered order b xs → Ordered order b ys →
    {eq : len ≡ (length xs + length ys)} →
    Ordered order b (merge order xs ys {eq})
merge-ordered _ [] _ _ p2 = p2
merge-ordered {len = succ _} ord (x ∷ xs) [] (orderedCons .x p1 p2) _ =
    orderedCons x p1 $ merge-ordered ord xs [] p2 orderedNull
merge-ordered {len = succ len} ord (x ∷ xs) (y ∷ ys)
    (orderedCons .x p1 p2) (orderedCons .y p3 p4)
        with DecidableOrder.decide ord x y
... | x≤y ∨- = orderedCons x p1 $
    merge-ordered {len = len} ord xs (y ∷ ys) p2 (orderedCons y x≤y p4)
... | -∨ x≰y = orderedCons y p3 $
    merge-ordered {len = len} ord (x ∷ xs) ys
        (orderedCons x (trichotomy' ord x≰y) p2) p4
merge-ordered {len = 0} _ (_ ∷ _) _ _ _ {()}

merge-ordered' :
    ∀ {i} {A : Set i} {op : Rel A i} {b : A} →
    (order : DecidableOrder op) → (xs ys : List A) →
    Ordered order b xs → Ordered order b ys →
    Ordered order b (merge' order xs ys)
merge-ordered' ord xs ys ox oy = merge-ordered ord xs ys ox oy

mergePair-ordered :
    ∀ {i} {A : Set i} {op : Rel A i} {b : A} →
    (order : DecidableOrder op) → (l : List (List A)) →
    All (Ordered order b) l → All (Ordered order b) (mergePair order l)
mergePair-ordered _ [] [] = []
mergePair-ordered _ (x ∷ []) (p ∷ nullSeq) = p ∷ nullSeq
mergePair-ordered ord (x ∷ x' ∷ xs) (p ∷ p' ∷ p'') =
    merge-ordered' ord x x' p p' ∷ mergePair-ordered ord xs p''

mergeAll-ordered :
    ∀ {i} {A : Set i} {op : Rel A i} {b : A} {n : Nat} →
    (order : DecidableOrder op) → (l : List (List A)) →
    {rel : length l ≤ n} → All (Ordered order b) l →
    Ordered order b (mergeAll order l {rel})
mergeAll-ordered _ [] [*] = orderedNull
mergeAll-ordered ord (x ∷ []) (p ∷ _) = p
mergeAll-ordered {n = succ n} ord (x ∷ x' ∷ xs) {≤succ rel} ordseq =
    mergeAll-ordered {n = n} ord (mergePair ord (x ∷ x' ∷ xs))
        (mergePair-ordered ord (x ∷ x' ∷ xs) ordseq)
mergeAll-ordered {n = 0} _ (_ ∷ _) {()} _

mergeAll-ordered' :
    ∀ {i} {A : Set i} {op : Rel A i} {b : A} →
    (order : DecidableOrder op) → (l : List (List A)) →
    All (Ordered order b) l → Ordered order b (mergeAll' order l)
mergeAll-ordered' ord l ordseq =
    mergeAll-ordered {n = length l} ord l {≤refl} ordseq

mergesort-ordered :
    ∀ {i} {A : Set i} {op : Rel A i} {b : A} →
    (order : DecidableOrder op) → (l : List A) →
    All (op b) l → Ordered order b (mergesort order l)
mergesort-ordered {A = A} {op} {b} ord l ps =
    mergeAll-ordered' ord (map (\a → a ∷ []) l) (p l ps) where
    p : (l : List A) → All (op b) l →
        All (Ordered ord b) (map (\a → a ∷ []) l)
    p [] [] = []
    p (x ∷ xs) (p1 ∷ p2) = orderedCons x p1 orderedNull ∷ p xs p2

