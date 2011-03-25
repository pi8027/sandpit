
{-# OPTIONS --universe-polymorphism #-}

module Data.TList where

open import Level
open import Function
open import Data.List

infixr 40 _:*:_

data TList {a : Level} : [ Set a ] -> Set (lsucc a) where
    [*] : TList []
    _:*:_ : {t : Set a}{ts : [ Set a ]} -> t -> TList ts -> TList (t :: ts)

*foldr : ∀ {a b}{l : [ Set a ]}{B : Set b} ->
         (f : Set a -> Set b -> Set b) ->
         ((A' : Set a) -> (B' : Set b) -> A' -> B' -> f A' B') ->
         B -> TList l -> foldr f B l
*foldr f f' b [*] = b
*foldr {l = t :: ts} {B} f f' b (x :*: xs) =
    f' t (foldr f B ts) x (*foldr {l = ts} f f' b xs)

*foldl : ∀ {a b}{l : [ Set b ]}{A : Set a} ->
         (f : Set a -> Set b -> Set a) ->
         ((A' : Set a) -> (B' : Set b) -> A' -> B' -> f A' B') ->
         A -> TList l -> foldl f A l
*foldl f f' b [*] = b
*foldl {l = t :: ts} {B} f f' b (x :*: xs) =
    *foldl {l = ts} f f' (f' B t b x) xs

*map : ∀ {a b}{l : [ Set a ]} ->
      (f : Set a -> Set b) -> ((A' : Set a) -> A' -> f A') ->
      TList l -> TList (map f l)
*map {l = []} f f' [*] = [*]
*map {l = t :: ts} f f' (x :*: xs) = f' t x :*: *map f f' xs

