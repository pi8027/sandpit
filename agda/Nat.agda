
module Nat where

open import Logic
open import Function
open import Relation

data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero + b = b
succ a + b = succ $ a + b

data _<=_ : RelationOn Nat where
    <=zero : ∀ {n} -> zero <= n
    <=succ : ∀ {m n} -> m <= n -> succ m <= succ n

<=unsucc : ∀ {m n} -> succ m <= succ n -> m <= n
<=unsucc (<=succ rel) = rel

<=refl : ∀ {i} -> i <= i
<=refl {zero} = <=zero
<=refl {succ _} = <=succ <=refl

<=trans : ∀ {a b c} -> a <= b -> b <= c -> a <= c
<=trans <=zero p2 = <=zero
<=trans (<=succ p1) (<=succ p2) = <=succ $ <=trans p1 p2

<=total : ∀ {a b} -> (a <= b) ∨ (b <= a)
<=total {a = zero} = orLeft <=zero
<=total {b = zero} = orRight <=zero
<=total {succ a} {succ b} = orMap <=succ <=succ <=total

<=decide : (a b : Nat) -> (a <= b) ∨ ¬ (a <= b)
<=decide zero _ = orLeft <=zero
<=decide (succ a) zero = orRight f where
    f : ¬ (succ a <= zero)
    f ()
<=decide (succ a) (succ b) =
    orMap <=succ (flip _∘_ <=unsucc) $ <=decide a b

<=Order : Order _<=_
<=Order = record { refl = <=refl ; trans = <=trans }

<=TotalOrder : TotalOrder _<=_
<=TotalOrder = record { base = <=Order ; total = <=total }

<=DecidableOrder : DecidableOrder _<=_
<=DecidableOrder = record { base = <=TotalOrder ; decide = <=decide }

<=reflSucc : ∀ {i} -> i <= succ i
<=reflSucc {zero} = <=zero
<=reflSucc {succ _} = <=succ <=reflSucc

data NatEq : RelationOn Nat where
    eqZero : NatEq zero zero
    eqSucc : ∀ {m n} -> NatEq m n -> NatEq (succ m) (succ n)

natEqRefl : ∀ {i} -> NatEq i i
natEqRefl {zero} = eqZero
natEqRefl {succ a} = eqSucc $ natEqRefl {a}

natEqTrans : ∀ {a b c} -> NatEq a b -> NatEq b c -> NatEq a c
natEqTrans eqZero eqZero = eqZero
natEqTrans (eqSucc a) (eqSucc b) = eqSucc $ natEqTrans a b

succAREq : ∀ {a a' b b'} ->
           NatEq a a' -> NatEq b b' -> NatEq (a + succ b) (succ (a' + b'))
succAREq eqZero eq = eqSucc eq
succAREq (eqSucc eq1) eq2 = eqSucc $ succAREq eq1 eq2

