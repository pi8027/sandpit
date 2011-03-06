
module List where

open import Ord

infixr 40 _::_

data List (A : Set) : Set where
    []   : List A
    _::_ : A -> List A -> List A

data CompareList (A : Set) (Co : Relation A A) :
        Relation (List A) (List A) where
    nullIsMinimal : forall {l} -> CompareList A Co [] l
    liftCons : forall {x y xs ys} -> Co x y -> Co y x ->
        CompareList A Co xs ys -> CompareList A Co (x :: xs) (y :: ys)
    headCompare : forall {x y : A}{xs ys : List A} ->
        Co x y -> (Co y x -> False) -> CompareList A Co (x :: xs) (y :: ys)

ListOrder : {A : Set} ->
    (f : Relation A A) ->
    OrderRelation A f ->
    OrderRelation (List A) (CompareList A f)
ListOrder {A} f elemorder = record { refl = listRefl ; trans = listTrans } where
    elemrefl : (i : A) -> f i i
    elemrefl = OrderRelation.refl elemorder

    elemtrans : (a b c : A) -> f a b -> f b c -> f a c
    elemtrans = OrderRelation.trans elemorder

    listRefl : (l : List A) -> CompareList A f l l
    listRefl [] = nullIsMinimal {l = []}
    listRefl (x :: xs) = liftCons (elemrefl x) (elemrefl x) (listRefl xs)

    listTrans : (a b c : List A) ->
        CompareList A f a b -> CompareList A f b c -> CompareList A f a c
    listTrans [] b c _ _ = nullIsMinimal {l = c}
    listTrans (a :: as) [] c () p2
    listTrans a (b :: bs) [] p1 ()
    listTrans (a :: as) (b :: bs) (c :: cs)
        (liftCons p1 p2 p3) (liftCons p4 p5 p6) =
        liftCons (elemtrans a b c p1 p4) (elemtrans c b a p5 p2)
            (listTrans as bs cs p3 p6)
    listTrans (a :: as) (b :: bs) (c :: cs)
        (headCompare p1 p2) (headCompare p3 p4) =
        headCompare (elemtrans a b c p1 p3) (\p -> p4 (elemtrans c a b p p1))
    listTrans (a :: as) (b :: bs) (c :: cs)
        (liftCons p1 p2 p3) (headCompare p4 p5) =
        headCompare (elemtrans a b c p1 p4) (\p -> p5 (elemtrans c a b p p1))
    listTrans (a :: as) (b :: bs) (c :: cs)
        (headCompare p1 p2) (liftCons p3 p4 p5) =
        headCompare (elemtrans a b c p1 p3) (\p -> p2 (elemtrans b c a p3 p))

