
{-# OPTIONS --universe-polymorphism #-}

module Group.Bool where

open import Data.Bool
open import Group
open import Relation.Binary.Equal

&&assoc : ∀ {a b c} → (a && (b && c)) ≡ ((a && b) && c)
&&assoc {false} = ≡refl
&&assoc {true} = ≡refl

&&comm : ∀ {a b} → (a && b) ≡ (b && a)
&&comm {false} {false} = ≡refl
&&comm {false} {true} = ≡refl
&&comm {true} {false} = ≡refl
&&comm {true} {true} = ≡refl

&&idleft : ∀ {a} → (true && a) ≡ a
&&idleft = ≡refl

&&idright : ∀ {a} → (a && true) ≡ a
&&idright {false} = ≡refl
&&idright {true} = ≡refl 

&&Semigroup : Semigroup _≡_ _&&_
&&Semigroup = semigroup ≡Equal (\{a} → &&assoc {a})

&&CSemigroup : CSemigroup _≡_ _&&_
&&CSemigroup = csemigroup &&Semigroup (\{a} → &&comm {a})

&&Monoid : Monoid _≡_ _&&_ true
&&Monoid = monoid &&Semigroup &&idleft &&idright

&&CMonoid : CMonoid _≡_ _&&_ true
&&CMonoid = cmonoid &&Monoid (\{a} → &&comm {a})

||assoc : ∀ {a b c} → (a || (b || c)) ≡ ((a || b) || c)
||assoc {false} = ≡refl
||assoc {true} = ≡refl

||comm : ∀ {a b} → (a || b) ≡ (b || a)
||comm {false} {false} = ≡refl
||comm {false} {true} = ≡refl
||comm {true} {false} = ≡refl
||comm {true} {true} = ≡refl

||idleft : ∀ {a} → (false || a) ≡ a
||idleft = ≡refl

||idright : ∀ {a} → (a || false) ≡ a
||idright {false} = ≡refl
||idright {true} = ≡refl

||Semigroup : Semigroup _≡_ _||_
||Semigroup = semigroup ≡Equal (\{a} → ||assoc {a})

||CSemigroup : CSemigroup _≡_ _||_
||CSemigroup = csemigroup ||Semigroup (\{a} → ||comm {a})

||Monoid : Monoid _≡_ _||_ false
||Monoid = monoid ||Semigroup ||idleft ||idright

||CMonoid : CMonoid _≡_ _||_ false
||CMonoid = cmonoid ||Monoid (\{a} → ||comm {a})

