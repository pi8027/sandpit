
module Mergesort where

open import Logic
open import Function
open import Relation
open import Nat
open import List
open import OList
open import Permutation

-- caseord : {A B : Set}{op : RelationOn A} ->
--           DecidableOrder op -> (x y : A) ->
--           (op x y -> B) -> (¬ op x y -> B) -> B
-- caseord order x y f g with DecidableOrder.decide order x y
-- ... | orLeft a = f a
-- ... | orRight b = g b

-- record SList {A : Set} {op : RelationOn A}
--              (order : DecidableOrder op) (b : A) (il : [ A ]) : Set where
--     field
--         l : [ A ]
--         o : ListIsOrdered order b l
--         p : Permutation il l

-- [#] : {A : Set}{op : RelationOn A}{order : DecidableOrder op}{b : A} ->
--       SList order b []
-- [#] = record {l = []; o = orderedNull; p = permNull}

-- _:#_#:_ : {A : Set}{op : RelationOn A}{order : DecidableOrder op}{b : A}{l : [ A ]} ->
--           (h : A) -> op b h -> SList order h l -> SList order b (h :: l)
-- x :# rel #: xs =
--     record {
--         l = x :: SList.l xs;
--         o = orderedCons x rel $ SList.o xs;
--         p = permSkip $ SList.p xs
--     }

permLength : {A : Set}{l1 l2 : [ A ]} ->
    Permutation l1 l2 -> NatEq (length l1) (length l2)
permLength permNull = eqZero
permLength (permSkip perm) = eqSucc $ permLength perm
permLength permSwap = eqSucc $ eqSucc natEqRefl
permLength (permTrans perm1 perm2) = natEqTrans (permLength perm1) (permLength perm2)

-- slistPermTrans :
--     {A : Set}{op : RelationOn A}{order : DecidableOrder op}{b : A}{l l' : [ A ]} ->
--     Permutation l l' -> SList order b l' -> SList order b l
-- slistPermTrans perm list =
--     record { l = SList.l list; o = SList.o list; p = permTrans perm $ SList.p list }

merge : {A : Set}{op : RelationOn A}{len : Nat} ->
        (order : DecidableOrder op) -> (xs ys : [ A ]) ->
        {eq : NatEq len (length xs + length ys)} -> [ A ]
merge order [] ys = ys
merge {len = succ len} order (x :: xs) [] {eqSucc eq} =
    x :: merge {len = len} order xs [] {eq}
merge {len = succ len} order (x :: xs) (y :: ys) {eqSucc eq}
    with DecidableOrder.decide order x y
... | orLeft _ = x :: merge order xs (y :: ys) {eq}
... | orRight _ = y :: merge order (x :: xs) ys
    {natEqTrans eq (succAREq {length xs} natEqRefl natEqRefl)}
merge {len = zero} _ (_ :: _) _ {()}

merge_ordered : {A : Set}{op : RelationOn A}{b : A}{len : Nat} ->
                (order : DecidableOrder op) -> (xs ys : [ A ]) ->
                ListIsOrdered order b xs -> ListIsOrdered order b ys ->
                {eq : NatEq len (length xs + length ys)} ->
                ListIsOrdered order b (merge order xs ys {eq})
merge_ordered order [] ys p1 p2 = p2
merge_ordered {len = succ len} order (x :: xs) [] (orderedCons .x p1 p2) p3 {eqSucc eq} =
    orderedCons x p1 $ merge order ordered xs [] p2 orderedNull
merge_ordered {len = succ len} order (x :: xs) (y :: ys)
    (orderedCons .x p1 p2) (orderedCons .y p3 p4) {eqSucc eq}
        with DecidableOrder.decide order x y
... | orLeft x<=y = orderedCons x p1 $
    merge_ordered {len = len} order xs (y :: ys) p2 (orderedCons y x<=y p4) {eq}
... | orRight !x<=y = orderedCons y p3 $ merge_ordered {len = len}
    order (x :: xs) ys (orderedCons x (trichotomy' order !x<=y) p2) p4
        {natEqTrans eq (succAREq {a = length xs} natEqRefl natEqRefl)}
merge_ordered {len = zero} _ (_ :: _) _ _ _ {()}

merge_permutation :
    {A : Set}{op : RelationOn A}{len : Nat} ->
    (order : DecidableOrder op) -> (xs ys : [ A ]) ->
    {eq : NatEq len (length xs + length ys)} ->
    Permutation (xs ++ ys) (merge order xs ys {eq})
merge_permutation order [] ys = permRefl
merge_permutation {len = succ len} order (x :: xs) [] {eqSucc eq} =
    permSkip $ merge order permutation xs []
merge_permutation {A = A} {len = succ len} order (x :: xs) (y :: ys) {eqSucc eq}
    with DecidableOrder.decide order x y
... | orLeft x<=y = permSkip $ merge_permutation {len = len} order xs (y :: ys) {eq}
... | orRight !x<=y = permTrans (gtrans {xs = x :: xs}) $ permSkip $
    merge_permutation {len = len} order (x :: xs) ys
        {natEqTrans eq (succAREq {a = length xs} natEqRefl natEqRefl)} where
    gtrans : {y : A}{xs ys : [ A ]} -> Permutation (xs ++ (y :: ys)) (y :: xs ++ ys)
    gtrans {xs = []} = permRefl
    gtrans {xs = x :: xs} = permTrans (permSkip (gtrans {xs = xs})) permSwap
merge_permutation {len = zero} _ (_ :: _) _ {()}

-- merge : {A : Set}{op : RelationOn A}{b : A}{len : Nat}{xs' ys' : [ A ]} ->
--         (order : DecidableOrder op) ->
--         (xs : SList order b xs') -> (ys : SList order b ys') ->
--         {eq : NatEq len (length xs' + length ys')} ->
--         SList order b (xs' ++ ys')
-- merge {xs' = []} {ys' = []} _ _ _ = [#]
-- merge {ys' = []} order l1 l2 = slistPermTrans permAppendNull l1
-- merge {xs' = []} order l1 l2 = l2
-- merge {len = zero} {xs' = _ :: _} _ _ _ {()}
-- merge {A} {op} {b} {succ len} {x' :: xs'} {y' :: ys'} order l1 l2 {eqSucc eq}
--     with SList.l l1 | SList.o l1 | SList.p l1 | SList.l l2 | SList.o l2 | SList.p l2
-- ... | [] | orderedNull | perm | _ | _ | _ = False-elim $ permFalse $ permSym perm
-- ... | _ | _ | _ | [] | orderedNull | perm = False-elim $ permFalse $ permSym perm
-- ... | x :: xs | orderedCons .x p1 p2 | px | y :: ys | orderedCons .y p3 p4 | py =
--     slistPermTrans (permAppend px py) $
--         caseord order x y f $ (slistPermTrans (gtrans {xs = x :: xs})) ∘ g where
--     f : op x y -> SList order b ((x :: xs) ++ (y :: ys))
--     f x<=y = x :# p1 #: merge {len = len} order
--          record { l = xs; o = p2; p = permRefl }
--          record { l = y :: ys; o = orderedCons y x<=y p4; p = permRefl }
--          {natEqTrans eq $ addEq (natEqDesucc (permLength px)) (permLength py)}
--     g : ¬ op x y -> SList order b (y :: ((x :: xs) ++ ys))
--     g !x<=y = y :# p3 #: merge {len = len} order
--          record { l = x :: xs; o = orderedCons x (trichotomy' order !x<=y) p2; p = permRefl }
--          record { l = ys; o = p4; p = permRefl }
--          {natEqTrans eq $ succAREq (natEqDesucc (permLength px)) (natEqDesucc (permLength py))}
--     gtrans : {y : A}{xs ys : [ A ]} -> Permutation (xs ++ (y :: ys)) (y :: xs ++ ys)
--     gtrans {xs = []} = permRefl
--     gtrans {y} {x :: xs} {ys} = permTrans (permSkip (gtrans {xs = xs})) permSwap

