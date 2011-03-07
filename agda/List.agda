
module List where

open import Ord

infixr 40 _::_

data List (A : Set) : Set where
    []   : List A
    _::_ : A -> List A -> List A

data CompareList {A : Set} (Co : Relation A A) :
        Relation (List A) (List A) where
    nullIsMinimal : forall {l} -> CompareList Co [] l
    consOrder : forall {x y xs ys} ->
        Co x y -> ((Co y x -> False) \/ CompareList Co xs ys) ->
        CompareList Co (x :: xs) (y :: ys)

ListOrder : {A : Set} ->
    (f : Relation A A) -> OrderRelation f -> OrderRelation (CompareList f)
ListOrder {A} f elemorder = record { refl = listRefl ; trans = listTrans } where
    elemtrans : {a b c : A} -> f a b -> f b c -> f a c
    elemtrans = OrderRelation.trans elemorder

    listRefl : forall {l} -> CompareList f l l
    listRefl {[]} = nullIsMinimal {l = []}
    listRefl {x :: xs} =
        consOrder (OrderRelation.refl elemorder) (orRight listRefl)

    listTrans : forall {a b c} ->
        CompareList f a b -> CompareList f b c -> CompareList f a c
    listTrans {a = []} _ _ = nullIsMinimal
    listTrans {a = _ :: _} {b = []} () p2
    listTrans {b = _ :: _} {c = []} p1 ()
    listTrans (consOrder p1 (orLeft p2)) (consOrder p3 _) =
        consOrder (elemtrans p1 p3) (orLeft (\p -> p2 (elemtrans p3 p)))
    listTrans (consOrder p1 _) (consOrder p2 (orLeft p3)) =
        consOrder (elemtrans p1 p2) (orLeft (\p -> p3 (elemtrans p p1)))
    listTrans (consOrder p1 (orRight p2)) (consOrder p3 (orRight p4)) =
        consOrder (elemtrans p1 p3) (orRight (listTrans p2 p4))

--data CompareList {A : Set} (Co : Relation A A) :
--        Relation (List A) (List A) where
--    nullIsMinimal : forall {l} -> CompareList Co [] l
--    consOrder : forall {x y xs ys} ->
--        SeqOrder Co (CompareList Co) x xs y ys ->
--        CompareList Co (x :: xs) (y :: ys)
--
--ListOrder : {A : Set} ->
--    (f : Relation A A) -> OrderRelation f -> OrderRelation (CompareList f)
--ListOrder {A} f elemorder = listorder where
--    mutual
--        listorder : OrderRelation (CompareList f)
--        listorder = record { refl = listRefl ; trans = listTrans }
--
--        listRefl : forall {l} -> CompareList f l l
--        listRefl {[]} = nullIsMinimal {l = []}
--        listRefl {x :: xs} = consOrder
--            (seqOrder (OrderRelation.refl elemorder) (orRight listRefl))
--
--        listTrans : forall {a b c} ->
--            CompareList f a b -> CompareList f b c -> CompareList f a c
--        listTrans {a = []} _ _ = nullIsMinimal
--        listTrans {a = _ :: _} {b = []} () p2
--        listTrans {b = _ :: _} {c = []} p1 ()
--        listTrans (consOrder p1) (consOrder p2) =
--            consOrder (seqOrderTrans elemorder listorder p1 p2)

