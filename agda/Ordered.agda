
module Ordered where

open import Relation
open import List

data Ordered {A : Set} {op : RelationOn A} (order : DecidableOrder op) :
             A -> [ A ] -> Set where
    orderedNull : {b : A} -> Ordered order b []
    orderedCons :
        {b : A}{l : [ A ]} ->
        (h : A) -> op b h -> Ordered order h l -> Ordered order b (h :: l)

