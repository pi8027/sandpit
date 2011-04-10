
{-# OPTIONS --universe-polymorphism #-}

module RE.List where

open import Function
open import Data.Empty
open import Data.Sum
open import Data.List
open import Data.List.Any
open import Data.List.All
open import Relation.Nullary

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

