
module Nat where

open import Logic
open import Function
open import Ord

data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

data _<=_ : Relation Nat Nat where
    zeroIsMinimal : forall {n} -> zero <= n
    liftSuccessor : forall {m n} -> (p : m <= n) -> succ m <= succ n

unliftSuccessor : forall {m n} -> succ m <= succ n -> m <= n
unliftSuccessor (liftSuccessor rel) = rel

NatOrder : (x : Nat) -> (y : Nat) -> Order _<=_ x y
NatOrder zero _ = leq zeroIsMinimal
NatOrder (succ x) zero = gt zeroIsMinimal f where
    f : succ x <= zero -> False
    f ()
NatOrder (succ x) (succ y) with NatOrder x y
... | leq x<=y = leq $ liftSuccessor x<=y
... | gt y<=x !x<=y = gt (liftSuccessor y<=x) (!x<=y ○ unliftSuccessor)

NatOrderLaws : OrderLaws _<=_
NatOrderLaws = record { refl = natRefl ; trans = natTrans } where
    natRefl : forall {i} -> i <= i
    natRefl {zero} = zeroIsMinimal
    natRefl {succ a} = liftSuccessor natRefl
    natTrans : forall {a b c} -> a <= b -> b <= c -> a <= c
    natTrans {a = zero} p1 p2 = zeroIsMinimal
    natTrans {succ _} {succ _} {succ _} (liftSuccessor p1) (liftSuccessor p2) =
        liftSuccessor $ natTrans p1 p2
    natTrans {a = succ _} {b = zero} () p2
    natTrans {b = succ _} {c = zero} p1 ()

