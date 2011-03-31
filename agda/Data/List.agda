
{-# OPTIONS --universe-polymorphism #-}

module Data.List where

open import Function
open import Logic
open import Types
open import Data.Nat
open import Relation.Binary.Core
open import Relation.Binary.Equal
open import Relation.Binary.Order

infixr 40 _∷_

data List {a} (A : Set a) : Set a where
    []   : List A
    _∷_ : A → List A → List A

foldr : ∀ {i j} {A : Set i} {B : Set j} → (A → B → B) → B → List A → B
foldr f b [] = b
foldr f b (x ∷ xs) = f x $ foldr f b xs

foldl : ∀ {i j} {A : Set i} {B : Set j} → (A → B → A) → A → List B → A
foldl f b [] = b
foldl f b (x ∷ xs) = foldl f (f b x) xs

map : ∀ {i j} {A : Set i} {B : Set j} → (A → B) → List A → List B
map f = foldr (_∷_ ∘ f) []

reverse : ∀ {i} {A : Set i} → List A → List A
reverse = foldl (flip _∷_) []

length : ∀ {i} {A : Set i} → List A → Nat
length = foldr (const succ) 0

_++_ : ∀ {i} {A : Set i} → List A → List A → List A
_++_ = flip $ foldr _∷_

concat : ∀ {i} {A : Set i} → List (List A) → List A
concat = foldr _++_ []

data Ordered {i} {A : Set i} {op : Rel A i}
             (ord : DecidableOrder op) : A → List A → Set i where
    orderedNull : {b : A} → Ordered ord b []
    orderedCons : {b : A} {l : List A} →
                  (h : A) → op b h → Ordered ord h l → Ordered ord b (h ∷ l)

-- Equality Relation

≡head : ∀ {i} {A : Set i} {x y : A} {xs ys : List A} →
         (x ∷ xs) ≡ (y ∷ ys) → x ≡ y
≡head ≡refl = ≡refl

≡tail : ∀ {i} {A : Set i} {x y : A} {xs ys : List A} →
         (x ∷ xs) ≡ (y ∷ ys) → xs ≡ ys
≡tail ≡refl = ≡refl

-- Order Relation

data LeqList {i} {A : Set i} (op : Rel A i) : Rel (List A) i where
    nullIsMinimal : ∀ {l} → LeqList op [] l
    consOrder : ∀ {x y xs ys} → op x y → (¬ op y x) ∨ LeqList op xs ys →
                LeqList op (x ∷ xs) (y ∷ ys)

ListOrder : ∀ {i} {A : Set i} →
            (op : Rel A i) → Order op → Order (LeqList op)
ListOrder op (order refl trans) = order listRefl listTrans where

    listRefl : ∀ {a} → LeqList op a a
    listRefl {[]} = nullIsMinimal
    listRefl {x ∷ xs} = consOrder refl (-∨ listRefl)

    listTrans : ∀ {a b c} → LeqList op a b → LeqList op b c → LeqList op a c
    listTrans {a = []} _ _ = nullIsMinimal
    listTrans {a = _ ∷ _} {b = []} () p2
    listTrans {b = _ ∷ _} {c = []} p1 ()
    listTrans (consOrder p1 (p2 ∨-)) (consOrder p3 _) =
        consOrder (trans p1 p3) ((p2 ∘ trans p3) ∨-)
    listTrans (consOrder p1 _) (consOrder p2 (p3 ∨-)) =
        consOrder (trans p1 p2) ((p3 ∘ flip trans p1) ∨-)
    listTrans (consOrder p1 (-∨ p2)) (consOrder p3 (-∨ p4)) =
        consOrder (trans p1 p3) (-∨ listTrans p2 p4)

ListTotalOrder : ∀ {i} {A : Set i} → (op : Rel A i) →
                 DecidableOrder op → TotalOrder (LeqList op)
ListTotalOrder {A = A} op (dorder (torder (order refl trans) total) decide) =
    torder (ListOrder op (order refl trans)) listTotal where

    listTotal : ∀ {a b} → LeqList op a b ∨ LeqList op b a
    listTotal {a = []} = nullIsMinimal ∨-
    listTotal {b = []} = -∨ nullIsMinimal
    listTotal {x ∷ xs} {y ∷ ys} with decide x y | decide y x
    ... | x≤y ∨- | y≤x ∨- =
        orMap (consOrder x≤y ∘ -∨_) (consOrder y≤x ∘ -∨_) listTotal
    ... | x≤y ∨- | -∨ y≰x = consOrder x≤y (y≰x ∨-) ∨-
    ... | -∨ x≰y | y≤x ∨- = -∨ consOrder y≤x (x≰y ∨-)
    ... | -∨ x≰y | -∨ y≰x = ⊥-elim $ orMerge x≰y y≰x total

ListDecidableOrder : ∀ {i} {A : Set i} → (op : Rel A i) →
                     DecidableOrder op → DecidableOrder (LeqList op)
ListDecidableOrder {A = A} op
        (dorder (torder (order refl trans) total) decide) =
    dorder
        (ListTotalOrder op (dorder (torder (order refl trans) total) decide))
        listDecide where

    listDecide : (a b : List A) → Decide (LeqList op a b)
    listDecide [] _ = nullIsMinimal ∨-
    listDecide (x ∷ xs) [] = -∨ \()
    listDecide (x ∷ xs) (y ∷ ys)
        with decide x y | decide y x | listDecide xs ys
    ... | x≤y ∨- | y≤x ∨- | xs≤ys ∨- = consOrder x≤y (-∨ xs≤ys) ∨-
    ... | x≤y ∨- | y≤x ∨- | -∨ xs≰ys = -∨ p where
        p : ¬ LeqList op (x ∷ xs) (y ∷ ys)
        p (consOrder _ p) = orMerge (flip id y≤x) xs≰ys p
    ... | x≤y ∨- | -∨ y≰x | _ = consOrder x≤y (y≰x ∨-) ∨-
    ... | -∨ x≰y | _ | _ = -∨ p where
        p : ¬ LeqList op (x ∷ xs) (y ∷ ys)
        p (consOrder x≤y _) = x≰y x≤y

