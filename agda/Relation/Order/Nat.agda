
module Relation.Order.Nat where

open import Function
open import Logic
open import Data.Nat
open import Relation
open import Relation.Order

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
