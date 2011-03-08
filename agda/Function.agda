
module Function where

_$_ : {a b : Set} -> (a -> b) -> a -> b
f $ a = f a

_○_ : {a b c : Set} -> (b -> c) -> (a -> b) -> a -> c
(f ○ g) a = f $ g a

flip : {a b c : Set} -> (a -> b -> c) -> b -> a -> c
flip f b a = f a b
