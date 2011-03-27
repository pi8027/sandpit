
{-# OPTIONS --universe-polymorphism #-}

module Group.Bool where

open import Data.Bool
open import Group
open import Relation.Equal

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
&&Semigroup =
    record {
        base = ≡Equal;
        assoc = \{a} → &&assoc {a}
    }

&&CSemigroup : CSemigroup _≡_ _&&_
&&CSemigroup =
    record {
        base = &&Semigroup;
        comm = \{a} → &&comm {a}
    }

&&Monoid : Monoid _≡_ _&&_ true
&&Monoid =
    record {
        base = &&Semigroup;
        idleft = &&idleft;
        idright = &&idright
    }

&&CMonoid : CMonoid _≡_ _&&_ true
&&CMonoid =
    record {
        base = &&Monoid;
        comm = \{a} → &&comm {a}
    }

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
||Semigroup =
    record {
        base = ≡Equal;
        assoc = \{a} → ||assoc {a}
    }

||CSemigroup : CSemigroup _≡_ _||_
||CSemigroup =
    record {
        base = ||Semigroup;
        comm = \{a} → ||comm {a}
    }

||Monoid : Monoid _≡_ _||_ false
||Monoid =
    record {
        base = ||Semigroup;
        idleft = ||idleft;
        idright = ||idright
    }

||CMonoid : CMonoid _≡_ _||_ false
||CMonoid =
    record {
        base = ||Monoid;
        comm = \{a} → ||comm {a}
    }

