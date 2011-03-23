
module Group.List where

open import Function
open import Data.List
open import Relation.Equal
open import Relation.Equal.List
open import Group

++assoc : ∀ {A}{a b c : [ A ]} -> (a ++ (b ++ c)) == ((a ++ b) ++ c)
++assoc {a = []} = ==refl
++assoc {a = x :: xs} = ==cons ==refl $ ++assoc {a = xs}

++idleft : ∀ {A}{a : [ A ]} -> ([] ++ a) == a
++idleft = ==refl

++idright : ∀ {A}{a : [ A ]} -> (a ++ []) == a
++idright {a = []} = ==refl
++idright {a = x :: xs} = ==cons ==refl ++idright

++Semigroup : ∀ {A} -> Semigroup {[ A ]} _==_ _++_
++Semigroup =
    record {
        base = ==Equal;
        assoc = \{a} -> ++assoc {a = a}
    }

++Monoid : ∀ {A} -> Monoid {[ A ]} _==_ _++_ []
++Monoid =
    record {
        base = ++Semigroup;
        idleft = ++idleft;
        idright = ++idright
    }

