
{-# OPTIONS --universe-polymorphism #-}

module RE.List where

open import Function
open import Data.Empty
open import Data.Sum
open import Data.List
open import Data.List.Any
open import Data.List.All
open import Relation.Nullary

anyLeft_++_ : ∀ {a p} {A : Set a} {P : A → Set p} {l1 : List A} →
                Any P l1 → (l2 : List A) → Any P (l1 ++ l2)
anyLeft here p ++ l = here p
anyLeft there p ++ l = there $ anyLeft p ++ l

anyRight_++_ : ∀ {a p} {A : Set a} {P : A → Set p} {l2 : List A} →
               (l1 : List A) → Any P l2 → Any P (l1 ++ l2)
anyRight [] ++ p = p
anyRight x ∷ xs ++ p = there $ anyRight xs ++ p

_all++_ : ∀ {a p} {A : Set a} {P : A → Set p} {l1 l2 : List A} →
          All P l1 → All P l2 → All P (l1 ++ l2)
[] all++ l = l
(x ∷ xs) all++ l = x ∷ (xs all++ l)

anyYesOrAllNo :
    ∀ {a p} {A : Set a} {P : A → Set p} →
    ((x : A) → Dec (P x)) → (l : List A) → Any P l ⊎ All (λ x → ¬ P x) l
anyYesOrAllNo dec [] = inj₂ []
anyYesOrAllNo dec (x ∷ xs) with dec x | anyYesOrAllNo dec xs
... | yes p | _ = inj₁ $ here p
... | _ | inj₁ p = inj₁ $ there p
... | no p1 | inj₂ p2 = inj₂ $ p1 ∷ p2

anyNoOrAllYes :
    ∀ {a p} {A : Set a} {P : A → Set p} →
    ((x : A) → Dec (P x)) → (l : List A) → Any (λ x → ¬ P x) l ⊎ All P l
anyNoOrAllYes dec [] = inj₂ []
anyNoOrAllYes dec (x ∷ xs) with dec x | anyNoOrAllYes dec xs
... | no p | _ = inj₁ $ here p
... | _ | inj₁ p = inj₁ $ there p
... | yes p1 | inj₂ p2 = inj₂ $ p1 ∷ p2

anyYesAllNo : ∀ {a p} {A : Set a} {P : A → Set p} {l : List A} →
              Any P l → All (λ x → ¬ P x) l → ⊥
anyYesAllNo (here p1) (p2 ∷ _) = p2 p1
anyYesAllNo (there p1) (_ ∷ p2) = anyYesAllNo p1 p2

anyConcatMap :
    ∀ {a b p q} {A : Set a} {B : Set b} {P : A → Set p} {Q : B → Set q} →
    (f : A → List B) → (∀ {x} → P x → Any Q (f x)) → (l : List A) →
    Any P l → Any Q (concatMap f l)
anyConcatMap f PtoQ [] ()
anyConcatMap f PtoQ (x ∷ xs) (here p) = anyLeft PtoQ p ++ concatMap f xs
anyConcatMap f PtoQ (x ∷ xs) (there p) =
    anyRight f x ++ anyConcatMap f PtoQ xs p

allConcatMap :
    ∀ {a b p q} {A : Set a} {B : Set b} {P : A → Set p} {Q : B → Set q} →
    (f : A → List B) → (∀ {x} → P x → All Q (f x)) → {l : List A} →
    All P l → All Q (concatMap f l)
allConcatMap f PtoQ [] = []
allConcatMap f PtoQ (p ∷ ps) = PtoQ p all++ allConcatMap f PtoQ ps

