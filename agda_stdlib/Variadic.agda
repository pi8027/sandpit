
module Variadic where

open import Data.Nat

variadic-type : ℕ → Set → Set → Set
variadic-type 0 A B = B
variadic-type (suc n) A B = A → variadic-type n A B

variadic-sum′ : (n : ℕ) → ℕ → variadic-type n ℕ ℕ
variadic-sum′ 0 sum = sum
variadic-sum′ (suc n) sum = λ m → variadic-sum′ n (sum + m)

variadic-sum : (n : ℕ) → variadic-type n ℕ ℕ
variadic-sum n = variadic-sum′ n 0

val : ℕ
val = variadic-sum 10 0 1 2 3 4 5 6 7 8 9
