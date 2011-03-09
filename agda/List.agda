
module List where

open import Function
open import Logic
open import Ord

infixr 40 _::_

data [_] (A : Set) : Set where
    []   : [ A ]
    _::_ : A -> [ A ] -> [ A ]

data CompareList {A : Set} (op : Relation A A) : Relation [ A ] [ A ] where
    nullIsMinimal : forall {l} -> CompareList op [] l
    consOrder : forall {x y xs ys} ->
        op x y -> ((op y x -> False) \/ CompareList op xs ys) ->
        CompareList op (x :: xs) (y :: ys)

unconsOrder : forall {A : Set}{op : Relation A A}{x xs y ys} ->
    CompareList op (x :: xs) (y :: ys) ->
    op x y /\ ((op y x -> False) \/ CompareList op xs ys)
unconsOrder (consOrder a b) = record {l = a ; r = b}

ListOrder : {A : Set}{op : Relation A A} ->
    ((x y : A) -> Order op x y) ->
    (xs ys : [ A ]) -> Order (CompareList op) xs ys
ListOrder elemorder [] _ = leq nullIsMinimal
ListOrder {op = op} elemorder (x :: xs) [] = gt f where
    f : CompareList op (x :: xs) [] -> False
    f ()
ListOrder {op = op} elemorder (x :: xs) (y :: ys) with elemorder x y
... | gt !x<=y = gt $ !x<=y ○ _/\_.l ○ unconsOrder
... | leq x<=y with elemorder y x
... | gt !y<=x = leq $ consOrder x<=y $ orLeft !y<=x
... | leq y<=x with ListOrder elemorder xs ys
... | leq xs<=ys = leq $ consOrder x<=y $ orRight xs<=ys
... | gt !xs<=ys = gt f where
    f : CompareList op (x :: xs) (y :: ys) -> False
    f (consOrder _ (orLeft !y<=x)) = !y<=x y<=x
    f (consOrder _ (orRight xs<=ys)) = !xs<=ys xs<=ys

ListOrderLaws : {A : Set} ->
    (op : Relation A A) -> OrderLaws op -> OrderLaws (CompareList op)
ListOrderLaws {A} op elemlaw =
        record { refl = listRefl ; trans = listTrans } where
    elemtrans : {a b c : A} -> op a b -> op b c -> op a c
    elemtrans = OrderLaws.trans elemlaw

    listRefl : forall {l} -> CompareList op l l
    listRefl {[]} = nullIsMinimal
    listRefl {x :: xs} =
        consOrder (OrderLaws.refl elemlaw) (orRight listRefl)

    listTrans : forall {a b c} ->
        CompareList op a b -> CompareList op b c -> CompareList op a c
    listTrans {a = []} _ _ = nullIsMinimal
    listTrans {a = _ :: _} {b = []} () p2
    listTrans {b = _ :: _} {c = []} p1 ()
    listTrans (consOrder p1 (orLeft p2)) (consOrder p3 _) =
        consOrder (elemtrans p1 p3) (orLeft (p2 ○ elemtrans p3))
    listTrans (consOrder p1 _) (consOrder p2 (orLeft p3)) =
        consOrder (elemtrans p1 p2) (orLeft (p3 ○ flip elemtrans p1))
    listTrans (consOrder p1 (orRight p2)) (consOrder p3 (orRight p4)) =
        consOrder (elemtrans p1 p3) (orRight (listTrans p2 p4))

