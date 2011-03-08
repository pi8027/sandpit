
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

ListOrderLaws : {A : Set} ->
    (op : Relation A A) -> OrderLaws op -> OrderLaws (CompareList op)
ListOrderLaws {A} op elemlaw =
        record { refl = listRefl ; trans = listTrans } where
    elemtrans : {a b c : A} -> op a b -> op b c -> op a c
    elemtrans = OrderLaws.trans elemlaw

    listRefl : forall {l} -> CompareList op l l
    listRefl {[]} = nullIsMinimal {l = []}
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

