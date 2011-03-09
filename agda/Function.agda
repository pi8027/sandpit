
module Function where

infixr 10 _$_

_$_ : {A B : Set} -> (A -> B) -> A -> B
f $ a = f a

infixr 90 _○_

_○_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
(f ○ g) a = f $ g a

flip : {A B C : Set} -> (A -> B -> C) -> B -> A -> C
flip f b a = f a b

id : {A : Set} -> A -> A
id a = a

const : {A B : Set} -> A -> B -> A
const a b = a

