
module Data.List where

open import Function
open import Logic
open import Data.Nat
open import Relation
open import Relation.Order

infixr 40 _::_

data [_] (A : Set) : Set where
    []   : [ A ]
    _::_ : A -> [ A ] -> [ A ]

foldr : ∀ {A B} -> (A -> B -> B) -> B -> [ A ] -> B
foldr f b [] = b
foldr f b (x :: xs) = f x $ foldr f b xs

foldl : ∀ {A B} -> (A -> B -> A) -> A -> [ B ] -> A
foldl f b [] = b
foldl f b (x :: xs) = foldl f (f b x) xs

map : ∀ {A B} -> (A -> B) -> [ A ] -> [ B ]
map f = foldr (_::_ ∘ f) []

reverse : ∀ {A} -> [ A ] -> [ A ]
reverse = foldl (flip _::_) []

length : ∀ {A} -> [ A ] -> Nat
length = foldr (const succ) zero

_++_ : ∀ {A} -> [ A ] -> [ A ] -> [ A ]
_++_ = flip $ foldr _::_

concat : ∀ {A} -> [ [ A ] ] -> [ A ]
concat = foldr _++_ []

data Sequence {A : Set} (p : A -> Set) : [ A ] -> Set where
    nullSeq : Sequence p []
    consSeq : ∀ {x xs} -> p x -> Sequence p xs -> Sequence p (x :: xs)

data Ordered {A : Set} {op : RelationOn A} (order : DecidableOrder op) :
             A -> [ A ] -> Set where
    orderedNull : {b : A} -> Ordered order b []
    orderedCons :
        {b : A}{l : [ A ]} ->
        (h : A) -> op b h -> Ordered order h l -> Ordered order b (h :: l)

