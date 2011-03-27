
{-# OPTIONS --universe-polymorphism #-}

module Group.Nat where

open import Function
open import Data.Nat
open import Relation.Equal
open import Relation.Equal.Nat
open import Relation.Transitive
open import Group

+assoc : ∀ {a b c} -> (a + (b + c)) ≡ ((a + b) + c)
+assoc {zero} = ≡refl
+assoc {succ a} = ≡apply' succ $ +assoc {a}

+comm : ∀ {a b} -> (a + b) ≡ (b + a)
+comm {zero} {zero} = ≡refl
+comm {zero} {succ b} = ≡apply' succ $ +comm {zero} {b}
+comm {succ a} {zero} = ≡apply' succ $ +comm {a} {zero}
+comm {succ a} {succ b} =
    ≡apply' succ $ ≡trans (+comm {a}) (addSuccReflexive {b})

+idleft : ∀ {a} -> (zero + a) ≡ a
+idleft = ≡refl

+idright : ∀ {a} -> (a + zero) ≡ a
+idright {a} = ≡trans (+comm {a} {zero}) +idleft

+Semigroup : Semigroup _≡_ _+_
+Semigroup =
    record {
        base = ≡Equal;
        assoc = \{a} -> +assoc {a}
    }

+CSemigroup : CSemigroup _≡_ _+_
+CSemigroup =
    record {
        base = +Semigroup;
        comm = \{a} -> +comm {a}
    }

+Monoid : Monoid _≡_ _+_ zero
+Monoid =
    record {
        base = +Semigroup;
        idleft = +idleft;
        idright = +idright
    }

+CMonoid : CMonoid _≡_ _+_ zero
+CMonoid =
    record {
        base = +Monoid;
        comm = \{a} -> +comm {a}
    }

natDistr : ∀ {a b c} -> ((a + b) * c) ≡ ((a * c) + (b * c))
natDistr {zero} = ≡refl
natDistr {succ a} {b} {c} = ≡trans ≡refl $
    ≡trans (≡apply'' _+_ (≡refl {a = c}) (natDistr {a = a})) (+assoc {c})

*assoc : ∀ {a b c} -> (a * (b * c)) ≡ ((a * b) * c)
*assoc {zero} = ≡refl
*assoc {succ a} {b} {c} = ≡trans ≡refl $
    ≡trans (≡apply'' _+_ (≡refl {a = b * c}) (*assoc {a}))
        (≡sym (natDistr {b}))

*comm : ∀ {a b} -> (a * b) ≡ (b * a)
*comm {zero} {zero} = ≡refl
*comm {zero} {succ b} = *comm {zero} {b}
*comm {succ a} {b} = ≡trans ≡refl $
    ≡trans (≡apply'' _+_ (≡refl {a = b}) (*comm {a} {b})) (p a b)
    where
    p : (a b : Nat) -> (b + (b * a)) ≡ (b * succ a)
    p _ zero = ≡refl
    p a (succ b) = ≡trans ≡refl $ ≡apply' succ $
        ≡trans (+assoc {b} {a}) $
        ≡trans (≡apply'' _+_ (+comm {b}) ≡refl) $
        ≡trans (≡sym (+assoc {a}))
               (≡apply'' _+_ (≡refl {a = a}) (p a b))

*idleft : ∀ {a} -> (succ zero * a) ≡ a
*idleft {a} = ≡trans (+comm {a} {zero}) ≡refl

*idright : ∀ {a} -> (a * succ zero) ≡ a
*idright {a} = ≡trans (*comm {a} {succ zero}) *idleft

*Semigroup : Semigroup _≡_ _*_
*Semigroup =
    record {
        base = ≡Equal;
        assoc = \{a} -> *assoc {a}
    }

*CSemigroup : CSemigroup _≡_ _*_
*CSemigroup =
    record {
        base = *Semigroup;
        comm = \{a} -> *comm {a}
    }

*Monoid : Monoid _≡_ _*_ (succ zero)
*Monoid =
    record {
        base = *Semigroup;
        idleft = *idleft;
        idright = *idright
    }

*CMonoid : CMonoid _≡_ _*_ (succ zero)
*CMonoid =
    record {
        base = *Monoid;
        comm = \{a} -> *comm {a}
    }

