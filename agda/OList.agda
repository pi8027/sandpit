
module OList where

open import Logic
open import Function
open import Relation
open import Nat

data OList {A : Set} {op : RelationOn A}
           (ord : DecidableOrder op) : A -> Set where
    [#] : {b : A} -> OList ord b
    _:#_#:_ : {b : A} -> (h : A) -> op b h -> OList ord h -> OList ord b

olength : {A : Set}{op : RelationOn A}{b : A}{ord : DecidableOrder op} ->
          OList ord b -> Nat
olength [#] = zero
olength (_ :# _ #: t) = succ $ olength t
