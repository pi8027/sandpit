
module Nat where

open import Logic
open import Function
open import Relation

data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

data NatEq : RelationOn Nat where
    eqZero : NatEq zero zero
    eqSucc : forall {m n} -> NatEq m n -> NatEq (succ m) (succ n)

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

natEqRefl : forall {i} -> NatEq i i
natEqRefl {zero} = eqZero
natEqRefl {succ a} = eqSucc $ natEqRefl {a}

natEqTrans : forall {a b c} -> NatEq a b -> NatEq b c -> NatEq a c
natEqTrans eqZero eqZero = eqZero
natEqTrans (eqSucc a) (eqSucc b) = eqSucc $ natEqTrans a b

natEqSym : forall {a b} -> NatEq a b -> NatEq b a
natEqSym eqZero = eqZero
natEqSym (eqSucc r) = eqSucc $ natEqSym r

-- succAREq : forall {a b} -> NatEq (succ (a + b)) (a + succ b)
-- succAREq {zero} {b} = eqSucc natEqRefl
-- succAREq {succ a} {b} = eqSucc $ succAREq {a} {b}

-- succAREq' : forall {a b} -> NatEq (a + succ b) (succ (a + b))
-- succAREq' {a} {b} = natEqSym $ succAREq {a} {b}

succAREq : forall {a a' b b'} ->
    NatEq a a' -> NatEq b b' -> NatEq (a + succ b) (succ (a' + b'))
succAREq eqZero eq = eqSucc eq
succAREq (eqSucc eq1) eq2 = eqSucc $ succAREq eq1 eq2

addEq : forall {a b c d} -> NatEq a b -> NatEq c d -> NatEq (a + c) (b + d)
addEq eqZero eq = eq
addEq (eqSucc eq1) eq2 = eqSucc $ addEq eq1 eq2

natEqDesucc : forall {a b} -> NatEq (succ a) (succ b) -> NatEq a b
natEqDesucc (eqSucc eq) = eq
