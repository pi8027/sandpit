
{-# OPTIONS --universe-polymorphism #-}

module Data.TList where

open import Level
open import Function
open import Data.Nat
open import Data.List

infixr 40 _:*:_

data TList {i : Level} : [ Set i ] → Set (lsucc i) where
    [*] : TList []
    _:*:_ : {t : Set i} {ts : [ Set i ]} → t → TList ts → TList (t ∷ ts)

*foldr : ∀ {i j k} {l : [ Set i ]} {B : Set k} {tf : Set i → B → B} {b : B} →
         (g : B → Set j) →
         ({A : Set i} → {b : B} → A → g b → g (tf A b)) →
         g b → TList l → g (foldr tf b l)
*foldr _ _ gb [*] = gb
*foldr g f gb (x :*: xs) = f x (*foldr g f gb xs)

*foldl : ∀ {i j} {l : [ Set j ]} {A : Set i} {a : A} {tf : A → Set j → A} →
         (g : A → Set i) →
         ({a : A} → {B : Set j} → g a → B → g (tf a B)) →
         g a → TList l → g (foldl tf a l)
*foldl _ _ ga [*] = ga
*foldl g f ga (x :*: xs) = *foldl g f (f ga x) xs

*map : ∀ {i j} {l : [ Set i ]} {f : Set i → Set j} →
       ({A' : Set i} → A' → f A') → TList l → TList (map f l)
*map f' = *foldr TList (_:*:_ ∘ f') [*]

*reverse : ∀ {i} {l : [ Set i ]} → TList l → TList (reverse l)
*reverse l = *foldl TList (flip _:*:_) [*] l

_*++_ : ∀ {i} {l l' : [ Set i ]} → TList l → TList l' → TList (l ++ l')
_*++_ = flip $ *foldr TList _:*:_

*concat : ∀ {i} {l : [ [ Set i ] ]} → TList (map TList l) → TList (concat l)
*concat {l = []} [*] = [*]
*concat {l = t ∷ ts} (x :*: xs) = x *++ *concat {l = ts} xs

