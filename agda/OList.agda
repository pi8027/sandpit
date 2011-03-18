
module OList where

open import Logic
open import Function
open import Relation
open import List
open import Nat

data ListIsOrdered {A : Set} {op : RelationOn A} (order : DecidableOrder op) :
                   A -> [ A ] -> Set where
     orderedNull : {b : A} -> ListIsOrdered order b []
     orderedCons : {b : A}{l : [ A ]} ->
                   (h : A) -> op b h -> ListIsOrdered order h l ->
                   ListIsOrdered order b (h :: l)

record OList {A : Set} {op : RelationOn A} (order : DecidableOrder op) (b : A) :
             Set where
     field
         l : [ A ]
         o : ListIsOrdered order b l

[#] : {A : Set}{b : A}{op : RelationOn A}{order : DecidableOrder op} ->
      OList order b
[#] = record {l = [] ; o = orderedNull}

_:#_#:_ : {A : Set}{b : A}{op : RelationOn A}{order : DecidableOrder op} ->
          (h : A) -> op b h -> OList order h -> OList order b
x :# rel #: xs = record {l = x :: OList.l xs ; o = orderedCons x rel (OList.o xs)}
