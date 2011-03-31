
{-# OPTIONS --universe-polymorphism #-}

module Level where

data Level : Set where
    zero : Level
    succ : Level → Level

{-# BUILTIN LEVEL Level #-}
{-# BUILTIN LEVELZERO zero #-}
{-# BUILTIN LEVELSUC succ #-}

infixl 60 _⊔_

_⊔_ : Level → Level → Level
zero ⊔ j = j
succ i ⊔ zero = succ i
succ i ⊔ succ j = succ (i ⊔ j)

{-# BUILTIN LEVELMAX _⊔_ #-}

