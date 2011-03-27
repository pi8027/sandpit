
{-# OPTIONS --universe-polymorphism #-}

module Data.List where

open import Level
open import Function
open import Types
open import Data.Nat
open import Relation.Order

infixr 40 _∷_

data [_] {a : Level} (A : Set a) : Set a where
    []   : [ A ]
    _∷_ : A → [ A ] → [ A ]

foldr : ∀ {i j} {A : Set i} {B : Set j} → (A → B → B) → B → [ A ] → B
foldr f b [] = b
foldr f b (x ∷ xs) = f x $ foldr f b xs

foldl : ∀ {i j} {A : Set i} {B : Set j} → (A → B → A) → A → [ B ] → A
foldl f b [] = b
foldl f b (x ∷ xs) = foldl f (f b x) xs

map : ∀ {i j} {A : Set i} {B : Set j} → (A → B) → [ A ] → [ B ]
map f = foldr (_∷_ ∘ f) []

reverse : ∀ {i} {A : Set i} → [ A ] → [ A ]
reverse = foldl (flip _∷_) []

length : ∀ {i} {A : Set i} → [ A ] → Nat
length = foldr (const succ) zero

_++_ : ∀ {i} {A : Set i} → [ A ] → [ A ] → [ A ]
_++_ = flip $ foldr _∷_

concat : ∀ {i} {A : Set i} → [ [ A ] ] → [ A ]
concat = foldr _++_ []

data Ordered {i : Level} {A : Set i} {op : RelationOn A}
             (order : DecidableOrder op) : A → [ A ] → Set i where
    orderedNull : {b : A} → Ordered order b []
    orderedCons :
        {b : A}{l : [ A ]} →
        (h : A) → op b h → Ordered order h l → Ordered order b (h ∷ l)

