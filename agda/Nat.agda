
module Nat where

open import Bool
open import Ord

data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

_+_ : Nat -> Nat -> Nat
a + zero = a
a + succ b = succ a + b

_<_ : Nat -> Nat -> Bool
succ a < succ b = a < b
a < zero = false
zero < a = true

_<=_ : Nat -> Nat -> Bool
succ a <= succ b = a <= b
zero <= a = true
a <= zero = false

minus : (a : Nat) -> (b : Nat) -> isTrue (b <= a) -> Nat
minus a zero t = a
minus (succ a) (succ b) t = minus a b t
minus zero (succ b) ()

NatOrder : OrderRelation Nat
NatOrder = record { f = _<=_ ; refl = natRefl ; trans = natTrans } where
    natRefl : (a : Nat) -> isTrue (a <= a)
    natRefl zero = _
    natRefl (succ a) = natRefl a
    natTrans : (a b c : Nat) ->
        isTrue (a <= b) -> isTrue (b <= c) -> isTrue (a <= c)
    natTrans zero b c p1 p2 = _
    natTrans (succ a) (succ b) (succ c) p1 p2 = natTrans a b c p1 p2
    natTrans (succ a) zero c () p2
    natTrans (succ a) (succ b) zero p1 ()

