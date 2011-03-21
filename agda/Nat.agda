
module Nat where

open import Logic
open import Function
open import Relation

data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

data NatEq : RelationOn Nat where
    eqZero : NatEq zero zero
    eqSucc : ∀ {m n} -> NatEq m n -> NatEq (succ m) (succ n)

data _<=_ : RelationOn Nat where
    zeroIsMinimal : ∀ {n} -> zero <= n
    liftSucc : ∀ {m n} -> (p : m <= n) -> succ m <= succ n

unliftSucc : ∀ {m n} -> succ m <= succ n -> m <= n
unliftSucc (liftSucc rel) = rel

<=Order : Order _<=_
<=Order = record { refl = <=refl ; trans = <=trans } where

    <=refl : ∀ {i} -> i <= i
    <=refl {zero} = zeroIsMinimal
    <=refl {succ _} = liftSucc <=refl

    <=trans : ∀ {a b c} -> a <= b -> b <= c -> a <= c
    <=trans zeroIsMinimal p2 = zeroIsMinimal
    <=trans (liftSucc p1) (liftSucc p2) = liftSucc $ <=trans p1 p2

<=TotalOrder : TotalOrder _<=_
<=TotalOrder = record { base = <=Order ; total = <=total } where

    <=total : ∀ {a b} -> (a <= b) ∨ (b <= a)
    <=total {a = zero} = orLeft zeroIsMinimal
    <=total {b = zero} = orRight zeroIsMinimal
    <=total {succ a} {succ b} = orMap liftSucc liftSucc <=total

<=DecidableOrder : DecidableOrder _<=_
<=DecidableOrder = record { base = <=TotalOrder ; decide = <=decide } where

    <=decide : (a b : Nat) -> (a <= b) ∨ ¬ (a <= b)
    <=decide zero _ = orLeft zeroIsMinimal
    <=decide (succ a) zero = orRight f where
        f : ¬ (succ a <= zero)
        f ()
    <=decide (succ a) (succ b) =
        orMap liftSucc (flip _∘_ unliftSucc) $ <=decide a b

_+_ : Nat -> Nat -> Nat
zero + b = b
succ a + b = succ $ a + b

natEqRefl : ∀ {i} -> NatEq i i
natEqRefl {zero} = eqZero
natEqRefl {succ a} = eqSucc $ natEqRefl {a}

natEqTrans : ∀ {a b c} -> NatEq a b -> NatEq b c -> NatEq a c
natEqTrans eqZero eqZero = eqZero
natEqTrans (eqSucc a) (eqSucc b) = eqSucc $ natEqTrans a b

natEqSym : ∀ {a b} -> NatEq a b -> NatEq b a
natEqSym eqZero = eqZero
natEqSym (eqSucc r) = eqSucc $ natEqSym r

succAREq : ∀ {a a' b b'} ->
           NatEq a a' -> NatEq b b' -> NatEq (a + succ b) (succ (a' + b'))
succAREq eqZero eq = eqSucc eq
succAREq (eqSucc eq1) eq2 = eqSucc $ succAREq eq1 eq2

