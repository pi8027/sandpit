
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

anyMap⁺ : ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p}
          {f : A → B} {xs} → Any (P ∘ f) xs → Any P (Data.List.map f xs)
anyMap⁺ (here p) = here p
anyMap⁺ (there p) = there $ anyMap⁺ p

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

splits : ∀ {a} {A : Set a} → List A → List (List (List A))
splits [] = [ [] ]
splits {A = A} (x ∷ xs) = concatMap f $ splits xs where
    f : List (List A) → List (List (List A))
    f [] = [ [ [ x ] ] ]
    f (y ∷ ys) = ([ x ] ∷ y ∷ ys) ∷ ((x ∷ y) ∷ ys) ∷ []

splitsInvConcat :
    ∀ {a} {A : Set a} → (l : List (List A)) →
    All (λ l → ¬ ListEmpty l) l → Any (_≡_ l) (splits (concat l))
splitsInvConcat [] _ = here refl
splitsInvConcat ((x ∷ xs) ∷ xss) (p ∷ ps) = any10 where
    any1 : Any (_≡_ xss) (splits (concat xss))
    any1 = splitsInvConcat xss ps
    any10 : Any (_≡_ ((x ∷ xs) ∷ xss)) (splits (concat ((x ∷ xs) ∷ xss)))
    any10 = {!!}
splitsInvConcat ([] ∷ _) (p ∷ _) = ⊥-elim $ p listEmpty

