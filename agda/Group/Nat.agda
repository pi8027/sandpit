
{-# OPTIONS --universe-polymorphism #-}

module Group.Nat where

open import Function
open import Data.Nat
open import Relation.Binary.Equal
open import Group

+assoc : ∀ {a b c} → (a + (b + c)) ≡ ((a + b) + c)
+assoc {0} = ≡refl
+assoc {succ a} = ≡apply' succ $ +assoc {a}

+comm : ∀ {a b} → (a + b) ≡ (b + a)
+comm {0} {0} = ≡refl
+comm {0} {succ b} = ≡apply' succ $ +comm {0} {b}
+comm {succ a} {0} = ≡apply' succ $ +comm {a} {0}
+comm {succ a} {succ b} = ≡apply' succ $ ≡trans (+comm {a}) (≡addSucc {b})

+idleft : ∀ {a} → (0 + a) ≡ a
+idleft = ≡refl

+idright : ∀ {a} → (a + 0) ≡ a
+idright {a} = ≡trans (+comm {a} {0}) +idleft

+Semigroup : Semigroup _≡_ _+_
+Semigroup = semigroup ≡Equal (\{a} → +assoc {a})

+CSemigroup : CSemigroup _≡_ _+_
+CSemigroup = csemigroup +Semigroup (\{a} → +comm {a})

+Monoid : Monoid _≡_ _+_ 0
+Monoid = monoid +Semigroup +idleft +idright

+CMonoid : CMonoid _≡_ _+_ 0
+CMonoid = cmonoid +Monoid (\{a} → +comm {a})

natDistr : ∀ {a b c} → ((a + b) * c) ≡ ((a * c) + (b * c))
natDistr {0} = ≡refl
natDistr {succ a} {b} {c} = ≡trans ≡refl $
    ≡trans (≡apply'' _+_ (≡refl {a = c}) (natDistr {a = a})) (+assoc {c})

*assoc : ∀ {a b c} → (a * (b * c)) ≡ ((a * b) * c)
*assoc {0} = ≡refl
*assoc {succ a} {b} {c} = ≡trans ≡refl $
    ≡trans (≡apply'' _+_ (≡refl {a = b * c}) (*assoc {a})) (≡sym (natDistr {b}))

*comm : ∀ {a b} → (a * b) ≡ (b * a)
*comm {0} {0} = ≡refl
*comm {0} {succ b} = *comm {0} {b}
*comm {succ a} {b} = ≡trans ≡refl $
    ≡trans (≡apply'' _+_ (≡refl {a = b}) (*comm {a} {b})) (p a b)
    where
    p : (a b : Nat) → (b + (b * a)) ≡ (b * succ a)
    p _ 0 = ≡refl
    p a (succ b) = ≡trans ≡refl $ ≡apply' succ $
        ≡trans (+assoc {b} {a}) $
        ≡trans (≡apply'' _+_ (+comm {b}) ≡refl) $
        ≡trans (≡sym (+assoc {a}))
               (≡apply'' _+_ (≡refl {a = a}) (p a b))

*idleft : ∀ {a} → (1 * a) ≡ a
*idleft {a} = ≡trans (+comm {a} {0}) ≡refl

*idright : ∀ {a} → (a * 1) ≡ a
*idright {a} = ≡trans (*comm {a} {1}) *idleft

*Semigroup : Semigroup _≡_ _*_
*Semigroup = semigroup ≡Equal (\{a} → *assoc {a})

*CSemigroup : CSemigroup _≡_ _*_
*CSemigroup = csemigroup *Semigroup (\{a} → *comm {a})

*Monoid : Monoid _≡_ _*_ 1
*Monoid = monoid *Semigroup *idleft *idright

*CMonoid : CMonoid _≡_ _*_ 1
*CMonoid = cmonoid *Monoid (\{a} → *comm {a})

