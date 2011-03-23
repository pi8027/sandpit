
module Group.Nat where

open import Function
open import Data.Nat
open import Relation.Equal
open import Relation.Equal.Nat
open import Group

+assoc : ∀ {a b c} -> (a + (b + c)) == ((a + b) + c)
+assoc {zero} = ==refl
+assoc {succ a} = ==succ $ +assoc {a}

+comm : ∀ {a b} -> (a + b) == (b + a)
+comm {zero} {zero} = ==refl
+comm {zero} {succ b} = ==succ $ +comm {zero} {b}
+comm {succ a} {zero} = ==succ $ +comm {a} {zero}
+comm {succ a} {succ b} = ==succ $ ==trans (+comm {a}) (addSuccReflexive {b})

+idleft : ∀ {a} -> (zero + a) == a
+idleft = ==refl

+idright : ∀ {a} -> (a + zero) == a
+idright {a} = ==trans (+comm {a} {zero}) +idleft

+Semigroup : Semigroup _==_ _+_
+Semigroup =
    record {
        base = ==Equal;
        assoc = (\{a} -> +assoc {a})
    }

+CSemigroup : CSemigroup _==_ _+_
+CSemigroup =
    record {
        base = +Semigroup;
        comm = (\{a} -> +comm {a})
    }

+Monoid : Monoid _==_ _+_ zero
+Monoid =
    record {
        base = +Semigroup;
        idleft = +idleft;
        idright = +idright
    }

+CMonoid : CMonoid _==_ _+_ zero
+CMonoid =
    record {
        base = +Monoid;
        comm = (\{a} -> +comm {a})
    }