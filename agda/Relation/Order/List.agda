
{-# OPTIONS --universe-polymorphism #-}

module Relation.Order.List where

open import Level
open import Function
open import Logic
open import Types
open import Data.List
open import Relation.Order

data LeqList {i : Level} {A : Set i} (op : RelationOn A) :
             RelationOn [ A ] where
    nullIsMinimal : ∀ {l} -> LeqList op [] l
    consOrder : ∀ {x y xs ys} -> op x y -> (¬ op y x) ∨ LeqList op xs ys ->
                LeqList op (x ∷ xs) (y ∷ ys)

ListOrder : ∀ {i}{A : Set i} ->
            (op : RelationOn A) -> Order op -> Order (LeqList op)
ListOrder op elemord = record { refl = listRefl ; trans = listTrans } where

    elemtrans : ∀ {a b c} -> op a b -> op b c -> op a c
    elemtrans = Order.trans elemord

    listRefl : ∀ {a} -> LeqList op a a
    listRefl {[]} = nullIsMinimal
    listRefl {x ∷ xs} = consOrder (Order.refl elemord) (orRight listRefl)

    listTrans : ∀ {a b c} -> LeqList op a b -> LeqList op b c -> LeqList op a c
    listTrans {a = []} _ _ = nullIsMinimal
    listTrans {a = _ ∷ _} {b = []} () p2
    listTrans {b = _ ∷ _} {c = []} p1 ()
    listTrans (consOrder p1 (orLeft p2)) (consOrder p3 _) =
        consOrder (elemtrans p1 p3) (orLeft (p2 ∘ elemtrans p3))
    listTrans (consOrder p1 _) (consOrder p2 (orLeft p3)) =
        consOrder (elemtrans p1 p2) (orLeft (p3 ∘ flip elemtrans p1))
    listTrans (consOrder p1 (orRight p2)) (consOrder p3 (orRight p4)) =
        consOrder (elemtrans p1 p3) (orRight (listTrans p2 p4))

ListTotalOrder : ∀ {i}{A : Set i} -> (op : RelationOn A) ->
                 DecidableOrder op -> TotalOrder (LeqList op)
ListTotalOrder {A = A} op elemord =
    record {
        base = ListOrder op $ TotalOrder.base $ DecidableOrder.base elemord;
        total = listTotal
    } where

    elemtotal : ∀ {a b} -> op a b ∨ op b a
    elemtotal {a} {b} = TotalOrder.total (DecidableOrder.base elemord) {a} {b}

    elemdecide : (a b : A) -> op a b ∨ (¬ op a b)
    elemdecide = DecidableOrder.decide elemord

    listTotal : ∀ {a b} -> LeqList op a b ∨ LeqList op b a
    listTotal {a = []} = orLeft nullIsMinimal
    listTotal {b = []} = orRight nullIsMinimal
    listTotal {x ∷ xs} {y ∷ ys} with elemdecide x y | elemdecide y x
    ... | orLeft x≤y | orLeft y≤x =
        orMap (consOrder x≤y ∘ orRight) (consOrder y≤x ∘ orRight) $
            listTotal {xs} {ys}
    ... | orLeft x≤y | orRight !y≤x = orLeft $ consOrder x≤y $ orLeft !y≤x
    ... | orRight !x≤y | orLeft y≤x = orRight $ consOrder y≤x $ orLeft !x≤y
    ... | orRight !x≤y | orRight !y≤x =
        ⊥-elim $ orMerge !x≤y !y≤x elemtotal

ListDecidableOrder : ∀ {i}{A : Set i} -> (op : RelationOn A) ->
                     DecidableOrder op -> DecidableOrder (LeqList op)
ListDecidableOrder {A = A} op elemord =
    record { base = ListTotalOrder op elemord; decide = listDecide } where

    elemdecide : (a b : A) -> op a b ∨ (¬ op a b)
    elemdecide = DecidableOrder.decide elemord

    listDecide : (a b : [ A ]) -> LeqList op a b ∨ (¬ LeqList op a b)
    listDecide [] _ = orLeft nullIsMinimal
    listDecide (x ∷ xs) [] = orRight f where
        f : ¬ LeqList op (x ∷ xs) []
        f ()
    listDecide (x ∷ xs) (y ∷ ys)
        with elemdecide x y | elemdecide y x | listDecide xs ys
    ... | orLeft x≤y | orLeft y≤x | orLeft xs≤ys =
        orLeft $ consOrder x≤y $ orRight xs≤ys
    ... | orLeft x≤y | orLeft y≤x | orRight !xs≤ys = orRight p where
        p : LeqList op (x ∷ xs) (y ∷ ys) -> ⊥
        p (consOrder _ (orLeft !y≤x)) = !y≤x y≤x
        p (consOrder _ (orRight xs≤ys)) = !xs≤ys xs≤ys
    ... | orLeft x≤y | orRight !y≤x | _ =
        orLeft $ consOrder x≤y $ orLeft !y≤x
    ... | orRight !x≤y | _ | _ = orRight p where
        p : LeqList op (x ∷ xs) (y ∷ ys) -> ⊥
        p (consOrder x≤y _) = !x≤y x≤y

