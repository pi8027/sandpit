
{-# OPTIONS --universe-polymorphism #-}

module Data.TList where

open import Level
open import Function
open import Data.List

infixr 40 _:*:_

data TList {i : Level} : [ Set i ] -> Set (lsucc i) where
    [*] : TList []
    _:*:_ : {t : Set i} {ts : [ Set i ]} -> t -> TList ts -> TList (t ∷ ts)

*foldr : ∀ {i j} {l : [ Set i ]} {B : Set j} ->
         (f : Set i -> Set j -> Set j) ->
         ((A' : Set i) -> (B' : Set j) -> A' -> B' -> f A' B') ->
         B -> TList l -> foldr f B l
*foldr f f' b [*] = b
*foldr {l = t ∷ ts} {B} f f' b (x :*: xs) =
    f' t (foldr f B ts) x (*foldr {l = ts} f f' b xs)

*foldl : ∀ {i j} {l : [ Set j ]} {A : Set i} ->
         (f : Set i -> Set j -> Set i) ->
         ((A' : Set i) -> (B' : Set j) -> A' -> B' -> f A' B') ->
         A -> TList l -> foldl f A l
*foldl f f' b [*] = b
*foldl {l = t ∷ ts} {B} f f' b (x :*: xs) =
    *foldl {l = ts} f f' (f' B t b x) xs

*map : ∀ {i j} {l : [ Set i ]} ->
      (f : Set i -> Set j) -> ((A' : Set i) -> A' -> f A') ->
      TList l -> TList (map f l)
*map {l = []} f f' [*] = [*]
*map {l = t ∷ ts} f f' (x :*: xs) = f' t x :*: *map f f' xs

