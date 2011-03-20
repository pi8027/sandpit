
module Mergesort where

open import Logic
open import Function
open import Relation
open import Nat
open import List
open import OList
open import Permutation

caseord : {A B : Set}{op : RelationOn A} ->
          DecidableOrder op -> (x y : A) ->
          (op x y -> B) -> (¬ op x y -> B) -> B
caseord order x y f g = orMerge f g $ DecidableOrder.decide order x y

record SList {A : Set} {op : RelationOn A}
             (order : DecidableOrder op) (b : A) (il : [ A ]) : Set where
    field
        l : [ A ]
        o : ListIsOrdered order b l
        p : Permutation il l

[#] : {A : Set}{op : RelationOn A}{order : DecidableOrder op}{b : A} ->
      SList order b []
[#] = record {l = []; o = orderedNull; p = permNull}

_:#_#:_ : {A : Set}{op : RelationOn A}{order : DecidableOrder op}{b : A}{l : [ A ]} ->
          (h : A) -> op b h -> SList order h l -> SList order b (h :: l)
x :# rel #: xs =
    record {
        l = x :: SList.l xs;
        o = orderedCons x rel $ SList.o xs;
        p = permSkip $ SList.p xs
    }

permLength : {A : Set}{l1 l2 : [ A ]} ->
    Permutation l1 l2 -> NatEq (length l1) (length l2)
permLength permNull = eqZero
permLength (permSkip perm) = eqSucc $ permLength perm
permLength permSwap = eqSucc $ eqSucc natEqRefl
permLength (permTrans perm1 perm2) = natEqTrans (permLength perm1) (permLength perm2)

slistPermTrans :
    {A : Set}{op : RelationOn A}{order : DecidableOrder op}{b : A}{l l' : [ A ]} ->
    Permutation l l' -> SList order b l' -> SList order b l
slistPermTrans perm list =
    record { l = SList.l list; o = SList.o list; p = permTrans perm $ SList.p list }

merge : {A : Set}{op : RelationOn A}{b : A}{len : Nat}{xs' ys' : [ A ]} ->
        (order : DecidableOrder op) ->
        (xs : SList order b xs') -> (ys : SList order b ys') ->
        {eq : NatEq len (length xs' + length ys')} ->
        SList order b (xs' ++ ys')
merge {xs' = []} {ys' = []} _ _ _ = [#]
merge {ys' = []} order l1 l2 = slistPermTrans permAppendNull l1
merge {xs' = []} order l1 l2 = l2
merge {len = zero} {xs' = _ :: _} _ _ _ {()}
merge {A} {op} {b} {succ len} {x' :: xs'} {y' :: ys'} order l1 l2 {eqSucc eq}
    with SList.l l1 | SList.o l1 | SList.p l1 | SList.l l2 | SList.o l2 | SList.p l2
... | [] | orderedNull | perm | _ | _ | _ = False-elim $ permFalse $ permSym perm
... | _ | _ | _ | [] | orderedNull | perm = False-elim $ permFalse $ permSym perm
... | x :: xs | orderedCons .x p1 p2 | px | y :: ys | orderedCons .y p3 p4 | py =
    slistPermTrans (permAppend px py) $
        caseord order x y f $ (slistPermTrans (gtrans {xs = x :: xs})) ∘ g where
    f : op x y -> SList order b ((x :: xs) ++ (y :: ys))
    f x<=y =
        x :# p1 #: merge {len = len} order
             record { l = xs; o = p2; p = permRefl }
             record { l = y :: ys; o = orderedCons y x<=y p4; p = permRefl }
             {natEqTrans eq $ addEq (natEqDesucc (permLength px)) (permLength py)}
    g : ¬ op x y -> SList order b (y :: ((x :: xs) ++ ys))
    g !x<=y =
        y :# p3 #: merge {len = len} order
             record { l = x :: xs; o = orderedCons x (trichotomy' order !x<=y) p2; p = permRefl }
             record { l = ys; o = p4; p = permRefl }
             {natEqTrans eq $ succAREq (natEqDesucc (permLength px)) (natEqDesucc (permLength py))}
    gtrans : {y : A}{xs ys : [ A ]} -> Permutation (xs ++ (y :: ys)) (y :: xs ++ ys)
    gtrans {xs = []} = permRefl
    gtrans {y} {x :: xs} {ys} = permTrans (permSkip (gtrans {xs = xs})) permSwap

