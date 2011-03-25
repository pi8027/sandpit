
{-# OPTIONS --universe-polymorphism #-}

module Data.List where

open import Level
open import Function
open import Types
open import Data.Nat
open import Relation.Order

infixr 40 _::_

data [_] {a : Level} (A : Set a) : Set a where
    []   : [ A ]
    _::_ : A -> [ A ] -> [ A ]

foldr : ∀ {a b}{A : Set a}{B : Set b} -> (A -> B -> B) -> B -> [ A ] -> B
foldr f b [] = b
foldr f b (x :: xs) = f x $ foldr f b xs

foldl : ∀ {a b}{A : Set a}{B : Set b} -> (A -> B -> A) -> A -> [ B ] -> A
foldl f b [] = b
foldl f b (x :: xs) = foldl f (f b x) xs

map : ∀ {a b}{A : Set a}{B : Set b} -> (A -> B) -> [ A ] -> [ B ]
map f = foldr (_::_ ∘ f) []

reverse : ∀ {a}{A : Set a} -> [ A ] -> [ A ]
reverse = foldl (flip _::_) []

length : ∀ {a}{A : Set a} -> [ A ] -> Nat
length = foldr (const succ) zero

_++_ : ∀ {a}{A : Set a} -> [ A ] -> [ A ] -> [ A ]
_++_ = flip $ foldr _::_

concat : ∀ {a}{A : Set a} -> [ [ A ] ] -> [ A ]
concat = foldr _++_ []

data Ordered {a : Level} {A : Set a} {op : RelationOn A}
             (order : DecidableOrder op) : A -> [ A ] -> Set a where
    orderedNull : {b : A} -> Ordered order b []
    orderedCons :
        {b : A}{l : [ A ]} ->
        (h : A) -> op b h -> Ordered order h l -> Ordered order b (h :: l)

