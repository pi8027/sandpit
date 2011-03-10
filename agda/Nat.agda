
module Nat where

open import Logic
open import Function
open import Relation

data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

data _<=_ : RelationOn Nat where
    zeroIsMinimal : forall {n} -> zero <= n
    liftSuccessor : forall {m n} -> (p : m <= n) -> succ m <= succ n

unliftSuccessor : forall {m n} -> succ m <= succ n -> m <= n
unliftSuccessor (liftSuccessor rel) = rel

<=Order : Order _<=_
<=Order = record { refl = <=refl ; trans = <=trans } where
    <=refl : forall {i} -> i <= i
    <=refl {zero} = zeroIsMinimal
    <=refl {succ a} = liftSuccessor <=refl

    <=trans : forall {a b c} -> a <= b -> b <= c -> a <= c
    <=trans {a = zero} p1 p2 = zeroIsMinimal
    <=trans {succ _} {succ _} {succ _} (liftSuccessor p1) (liftSuccessor p2) =
        liftSuccessor $ <=trans p1 p2
    <=trans {a = succ _} {b = zero} () p2
    <=trans {b = succ _} {c = zero} p1 ()

<=TotalOrder : TotalOrder _<=_
<=TotalOrder = record { base = <=Order ; total = <=total } where
    <=total : forall {a b} -> (a <= b) \/ (b <= a)
    <=total {a = zero} = orLeft zeroIsMinimal
    <=total {b = zero} = orRight zeroIsMinimal
    <=total {succ a} {succ b} = orMap liftSuccessor liftSuccessor <=total

<=DecidableOrder : DecidableOrder _<=_
<=DecidableOrder = record { base = <=TotalOrder ; decide = <=decide } where
    <=decide : (a b : Nat) -> (a <= b) \/ (a <= b -> False)
    <=decide zero _ = orLeft zeroIsMinimal
    <=decide (succ a) (zero) = orRight f where
        f : succ a <= zero -> False
        f ()
    <=decide (succ a) (succ b) =
        orMap liftSuccessor (flip _○_ unliftSuccessor) $ <=decide a b

