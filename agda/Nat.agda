
module Nat where

open import Logic
open import Function
open import Relation

data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

data _<=_ : RelationOn Nat where
    zeroIsMinimal : forall {n} -> zero <= n
    liftSucc : forall {m n} -> (p : m <= n) -> succ m <= succ n

unliftSucc : forall {m n} -> succ m <= succ n -> m <= n
unliftSucc (liftSucc rel) = rel

<=Order : Order _<=_
<=Order = record { refl = <=refl ; trans = <=trans } where

    <=refl : forall {i} -> i <= i
    <=refl {zero} = zeroIsMinimal
    <=refl {succ _} = liftSucc <=refl

    <=trans : forall {a b c} -> a <= b -> b <= c -> a <= c
    <=trans zeroIsMinimal p2 = zeroIsMinimal
    <=trans (liftSucc p1) (liftSucc p2) = liftSucc $ <=trans p1 p2

<=TotalOrder : TotalOrder _<=_
<=TotalOrder = record { base = <=Order ; total = <=total } where

    <=total : forall {a b} -> (a <= b) ∨ (b <= a)
    <=total {a = zero} = orLeft zeroIsMinimal
    <=total {b = zero} = orRight zeroIsMinimal
    <=total {succ a} {succ b} = orMap liftSucc liftSucc <=total

<=DecidableOrder : DecidableOrder _<=_
<=DecidableOrder = record { base = <=TotalOrder ; decide = <=decide } where

    <=decide : (a b : Nat) -> (a <= b) ∨ (a <= b -> False)
    <=decide zero _ = orLeft zeroIsMinimal
    <=decide (succ a) zero = orRight f where
        f : succ a <= zero -> False
        f ()
    <=decide (succ a) (succ b) =
        orMap liftSucc (flip _∘_ unliftSucc) $ <=decide a b

