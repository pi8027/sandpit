
module Relation.Equal.Nat where

open import Function
open import Data.Nat
open import Relation.Equal

==succ : {n m : Nat} -> n == m -> succ n == succ m
==succ ==refl = ==refl

==desucc : {n m : Nat} -> succ n == succ m -> n == m
==desucc ==refl = ==refl

addSuccReflexive : {n m : Nat} -> (succ n + m) == (n + succ m)
addSuccReflexive {zero} = ==refl
addSuccReflexive {succ n} = ==succ $ addSuccReflexive {n}

