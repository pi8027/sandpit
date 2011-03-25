
{-# OPTIONS --universe-polymorphism #-}

module Types where

open import Level

BinOp : ∀ {a} -> Set a -> Set a
BinOp A = A -> A -> A

Relation : ∀ {a} -> Set a -> Set a -> Set (lsucc a)
Relation {a} A B = A -> B -> Set a

RelationOn : ∀ {a} -> Set a -> Set (lsucc a)
RelationOn A = Relation A A

