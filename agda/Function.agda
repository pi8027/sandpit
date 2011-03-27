
{-# OPTIONS --universe-polymorphism #-}

module Function where

open import Level

id : ∀ {a}{A : Set a} -> A -> A
id a = a

infixr 10 _$_

_$_ : ∀ {a b}{A : Set a}{B : Set b} -> (A -> B) -> A -> B
_$_ = id

infixr 90 _∘_

_∘_ : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c} ->
      (B -> C) -> (A -> B) -> A -> C
(f ∘ g) a = f $ g a
flip : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c} ->
       (A -> B -> C) -> B -> A -> C
flip f b a = f a b

const : ∀ {a b}{A : Set a}{B : Set b} -> A -> B -> A
const a _ = a

type-signature : ∀ {a} (A : Set a) -> A -> A
type-signature A x = x

syntax type-signature A x = x ∶ A

