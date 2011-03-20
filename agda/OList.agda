
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

