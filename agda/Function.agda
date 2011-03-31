                                   
{-# OPTIONS --universe-polymorphism #-}

module Function where

open import Level

id : ∀ {a} {A : Set a} → A → A
id a = a

infixr 10 _$_

_$_ : ∀ {a b} {A : Set a} {B : A → Set b} →
      ((x : A) → B x) → (x : A) → B x
_$_ = id

infixr 90 _∘_

_∘_ : ∀ {i j k} {A : Set i} {B : A → Set j} {C : {x : A} → B x → Set k} →
      (∀ {x} → (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘ g = \a → f $ g a

flip : ∀ {i j k} {A : Set i} {B : Set j} {C : A → B → Set k} →
       ((a : A) → (b : B) → C a b) → (b : B) → (a : A) → C a b
flip f b a = f a b

const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const a _ = a

_on_ : ∀ {i j k} {A : Set i} {B : A → Set j}
          {C : ∀ {x y} → B x → B y → Set k}
       (f : ∀ {x y} → (x' : B x) → (y' : B y) → C x' y') →
       (g : (a : A) → B a) → ((x : A) → (y : A) → C (g x) (g y))
_*_ on f = \x y → f x * f y

type-signature : ∀ {a} (A : Set a) → A → A
type-signature A x = x

