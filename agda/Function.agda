
{-# OPTIONS --universe-polymorphism #-}

module Function where

open import Level

infixr 10 _$_

_$_ : ∀ {a b}{A : Set a}{B : Set b} -> (A -> B) -> A -> B
f $ a = f a

infixr 90 _∘_

_∘_ : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c} ->
      (B -> C) -> (A -> B) -> A -> C
(f ∘ g) a = f $ g a
flip : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c} ->
       (A -> B -> C) -> B -> A -> C
flip f b a = f a b

id : ∀ {a}{A : Set a} -> A -> A
id a = a

const : ∀ {a b}{A : Set a}{B : Set b} -> A -> B -> A
const a b = a

