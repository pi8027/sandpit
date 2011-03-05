
module Nat where

open import Ord

data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

data _<=_ : Relation Nat Nat where
    zeroIsMinimal : forall { n } -> zero <= n
    liftSuccessor : forall { m n } (p : m <= n) -> succ m <= succ n

NatOrder : OrderRelation Nat _<=_
NatOrder = record { refl = natRefl ; trans = natTrans } where
    natRefl : (i : Nat) -> i <= i
    natRefl zero = zeroIsMinimal
    natRefl (succ a) = liftSuccessor (natRefl a)
    natTrans : (a b c : Nat) -> a <= b -> b <= c -> a <= c
    natTrans zero b c p1 p2 = zeroIsMinimal
    natTrans (succ a) (succ b) (succ c) (liftSuccessor p1) (liftSuccessor p2) =
        liftSuccessor (natTrans a b c p1 p2)
    natTrans (succ a) zero c () p2
    natTrans (succ a) (succ b) zero p1 ()

