
module Bool where

data Bool : Set where
    true : Bool
    false : Bool

data   False : Set where
record True  : Set where

isTrue : Bool -> Set
isTrue true = True
isTrue false = False

not : Bool -> Bool
not true = false
not false = true

_/\_ : Bool -> Bool -> Bool
true /\ true = true
_ /\ _ = false

_\/_ : Bool -> Bool -> Bool
false \/ false = false
_ \/ _ = true

