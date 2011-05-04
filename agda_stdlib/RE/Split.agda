
{-# OPTIONS --universe-polymorphism #-}

module RE.Split where

open import Function
open import Data.Product
open import Data.Empty
open import Data.List
open import Data.List.Any
open import Data.List.All
open import Data.List.All.Properties
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import RE.Core
open import RE.List

split : ∀ {a} {A : Set a} → List A → List (List A × List A)
split [] = [ ([] , []) ]
split (x ∷ xs) =
    ([] , x ∷ xs) ∷ Data.List.map (λ s → (x ∷ proj₁ s) , proj₂ s) (split xs)

splitInvAppend : ∀ {a} {A : Set a} → (ls rs : List A) →
                 Any (λ s → (ls ≡ proj₁ s) × (rs ≡ proj₂ s)) (split (ls ++ rs))
splitInvAppend [] [] = here (refl , refl)
splitInvAppend [] (r ∷ rs) = here (refl , refl)
splitInvAppend {a} {A} (l ∷ ls) rs =
    there $ anyMap⁺ $ Data.List.Any.map f $ splitInvAppend ls rs where
    f : ∀ {s : List A × List A} → ls ≡ proj₁ s × rs ≡ proj₂ s →
        _≡_ {a} {List A} (l ∷ ls) (l ∷ proj₁ s) × rs ≡ proj₂ s
    f (lp , rp) = cong₂ _∷_ (refl {x = l}) lp , rp

appendInvSplit : ∀ {a} {A : Set a} →
                 (l : List A) →  All (λ s → l ≡ uncurry′ _++_ s) (split l)
appendInvSplit [] = refl ∷ []
appendInvSplit {a} {A} (x ∷ xs) =
    refl ∷ All-map (Data.List.All.map (λ {s} → f {s}) (appendInvSplit xs)) where
    f : ∀ {s : List A × List A} → (xs ≡ proj₁ s ++ proj₂ s) →
        (_≡_ {a} {List A} (x ∷ xs) (x ∷ proj₁ s ++ proj₂ s))
    f p = cong₂ _∷_ refl p

splitsF : ∀ {a} {A : Set a} → A → List (List A) → List (List (List A))
splitsF x [] = [ [ [ x ] ] ]
splitsF x (y ∷ ys) = ([ x ] ∷ y ∷ ys) ∷ ((x ∷ y) ∷ ys) ∷ []

splits : ∀ {a} {A : Set a} → List A → List (List (List A))
splits [] = [ [] ]
splits {A = A} (x ∷ xs) = concatMap (splitsF x) $ splits xs

splitsInvConcat :
    ∀ {a} {A : Set a} → (l : List (List A)) →
    All (λ l → ¬ ListEmpty l) l → Any (_≡_ l) (splits (concat l))
splitsInvConcat [] _ = here refl
splitsInvConcat {A = A} ((x ∷ xs) ∷ xss) (p ∷ ps) = (h (x ∷ xs) λ ()) where
    f : {x : A} {xss' : List (List A)} →
        xss ≡ xss' → Any (_≡_ ((x ∷ []) ∷ xss)) (splitsF x xss')
    f refl with xss
    ... | [] = here refl
    ... | _ ∷ _ = here refl
    g : {x : A} {xs : List A} {xss' : List (List A)} →
        xs ∷ xss ≡ xss' → Any (_≡_ ((x ∷ xs) ∷ xss)) (splitsF x xss')
    g refl = there $ here refl
    h : (l : List A) → ¬ ListEmpty l →
        Any (_≡_ (l ∷ xss)) (splits (concat (l ∷ xss)))
    h [] p = ⊥-elim $ p listEmpty
    h (x ∷ []) _ = anyConcatMap (splitsF x) f
        (splits (concat xss)) (splitsInvConcat xss ps)
    h (x ∷ x' ∷ xs) _ = anyConcatMap (splitsF x) g
        (splits (concat ((x' ∷ xs) ∷ xss))) (h (x' ∷ xs) λ ())
splitsInvConcat ([] ∷ _) (p ∷ _) = ⊥-elim $ p listEmpty

concatInvSplits :
    ∀ {a} {A : Set a} → (l : List A) → All (λ l' → concat l' ≡ l) (splits l)
concatInvSplits [] = refl ∷ []
concatInvSplits {A = A} (x ∷ xs) =
        allConcatMap (splitsF x) (λ {x} → f {x}) (concatInvSplits xs) where
    f : {xss : List (List A)} →
        concat xss ≡ xs → All (λ xss' → concat xss' ≡ x ∷ xs) (splitsF x xss)
    f {xss} eq with xss | xs | eq
    ... | [] | [] | refl = refl ∷ []
    ... | [] | _ ∷ _ | ()
    ... | _ ∷ _ | _ | eq' = cong (_∷_ x) eq' ∷ cong (_∷_ x) eq' ∷ []

splitsAllNonEmpty :
    ∀ {a} {A : Set a} →
    (l : List A) → All (All (λ l' → ¬ ListEmpty l')) (splits l)
splitsAllNonEmpty [] = [] ∷ []
splitsAllNonEmpty {A = A} (x ∷ xs) =
    allConcatMap (splitsF x) f (splitsAllNonEmpty xs) where
    f : {xss : List (List A)} → All (λ l → ¬ ListEmpty l) xss →
        All (λ l → All (λ l' → ¬ ListEmpty l') l) (splitsF x xss)
    f [] = ((λ ()) ∷ []) ∷ []
    f (p ∷ ps) = ((λ ()) ∷ p ∷ ps) ∷ ((λ ()) ∷ ps) ∷ []

