
module Logic where

open import Function

data False : Set where

False-elim : {A : Set} -> False -> A
False-elim ()

¬_ : Set -> Set
¬ A = A -> False

data _∨_ (Left Right : Set) : Set where
    orLeft : Left -> Left ∨ Right
    orRight : Right -> Left ∨ Right

record _∧_ (Left Right : Set) : Set where
    field
        l : Left
        r : Right

andLeft : {Left Right : Set} -> Left ∧ Right -> Left
andLeft = _∧_.l

andRight : {Left Right : Set} -> Left ∧ Right -> Right
andRight = _∧_.r

orMerge : {Left Right A : Set} ->
    (Left -> A) -> (Right -> A) -> Left ∨ Right -> A
orMerge lf _ (orLeft left) = lf left
orMerge _ rf (orRight right) = rf right

orMap : {L L' R R' : Set} -> (L -> L') -> (R -> R') -> L ∨ R -> L' ∨ R'
orMap f g = orMerge (orLeft ∘ f) (orRight ∘ g)

