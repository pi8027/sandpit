
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
    listRefl : (l : List A) -> CompareList A f l l
    listRefl [] = nullIsMinimal {l = []}
    listRefl (x :: xs) = liftCons
        (OrderRelation.refl elemorder x) (OrderRelation.refl elemorder x)
        (listRefl xs)

    postulate
        listTrans_ : (a b c : List A) ->
            CompareList A f a b -> CompareList A f b c -> CompareList A f a c

    listTrans : (a b c : List A) ->
        CompareList A f a b -> CompareList A f b c -> CompareList A f a c
    listTrans [] b c _ _ = nullIsMinimal {l = c}
    listTrans (a :: as) [] c () p2
    listTrans a (b :: bs) [] p1 ()
    listTrans a b c p1 p2 = listTrans_ a b c p1 p2

