
module Logic where

data False : Set where

data _\/_ (Left : Set) (Right : Set) : Set where
    orLeft : Left -> Left \/ Right
    orRight : Right -> Left \/ Right

record _/\_ (Left : Set) (Right : Set) : Set where
    field
        l : Left
        r : Right

