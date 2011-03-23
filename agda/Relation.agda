
module Relation where

Relation : Set -> Set -> Set1
Relation A B = A -> B -> Set

RelationOn : Set -> Set1
RelationOn A = Relation A A

