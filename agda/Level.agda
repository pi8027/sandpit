
{-# OPTIONS --universe-polymorphism #-}

module Level where

data Level : Set where
  lzero : Level
  lsucc : Level → Level

{-# BUILTIN LEVEL Level #-}
{-# BUILTIN LEVELZERO lzero #-}
{-# BUILTIN LEVELSUC lsucc #-}

_⊔_ : Level → Level → Level
lzero ⊔ j = j
lsucc i ⊔ lzero = lsucc i
lsucc i ⊔ lsucc j = lsucc (i ⊔ j)

{-# BUILTIN LEVELMAX _⊔_ #-}

