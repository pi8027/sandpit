
{-# OPTIONS --universe-polymorphism #-}

module RE.Match where

open import Function
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Data.List
open import Data.List.All
open import Data.List.Any
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import RE.Core
open import RE.List
open import RE.Split

eqTyping : ∀ {t} {T1 T2 : Set t} → T1 ≡ T2 → T1 → T2
eqTyping refl a = a

match : ∀ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ} →
        Decidable _≈_ → Decidable (REMatch _≈_)
match _ reEmptySet _ = no λ ()
match _ reEmptyString [] = yes reMatchEmptyString
match _ reEmptyString (c ∷ cs) = no λ ()
match dec (reSingleton _) [] = no (λ ())
match {_≈_ = _≈_} dec (reSingleton c1) (c2 ∷ []) with dec c1 c2
... | yes c1≈c2 = yes $ reMatchSingleton c1≈c2
... | no ¬c1≈c2 = no f where
    f : ¬ REMatch _≈_ (reSingleton c1) (c2 ∷ [])
    f (reMatchSingleton c1≈c2) = ¬c1≈c2 c1≈c2
match dec (reSingleton _) (_ ∷ _ ∷ _) = no (λ ())
match {A = A} {_≈_} dec (reJoin re1 re2) str =
    [ yes ∘ f (split str) (appendInvSplit str) , no ∘ flip (anyYesAllNo ∘ g) ]′
        (anyYesOrAllNo joindec (split str)) where
    joindec : (s : List A × List A) →
              Dec (REMatch _≈_ re1 (proj₁ s) × REMatch _≈_ re2 (proj₂ s))
    joindec (ls , rs) with match dec re1 ls | match dec re2 rs
    ... | yes p1 | yes p2 = yes $ p1 , p2
    ... | no p | _ = no $ p ∘ proj₁
    ... | _ | no p = no $ p ∘ proj₂
    f : (l : List (List A × List A)) → All (λ s → str ≡ uncurry′ _++_ s) l →
        Any (λ s → REMatch _≈_ re1 (proj₁ s) × REMatch _≈_ re2 (proj₂ s)) l →
        REMatch _≈_ (reJoin re1 re2) str
    f [] _ ()
    f ((ls , rs) ∷ _) (p1 ∷ _) (here (p2 , p3)) = eqTyping
        (cong (REMatch _≈_ (reJoin re1 re2)) (sym p1)) (reMatchJoin p2 p3)
    f (_ ∷ xs) (_ ∷ p1) (there p2) = f xs p1 p2
    g : {str : List A} → REMatch _≈_ (reJoin re1 re2) str →
        Any (λ s → REMatch _≈_ re1 (proj₁ s) × REMatch _≈_ re2 (proj₂ s))
            (split str)
    g (reMatchJoin {s1 = s1} {s2} p1 p2) =
        Data.List.Any.map g' $ splitInvAppend s1 s2 where
        g' : {x : List A × List A} →
             (s1 ≡ proj₁ x) × (s2 ≡ proj₂ x) →
             REMatch _≈_ re1 (proj₁ x) × REMatch _≈_ re2 (proj₂ x)
        g' (eq1 , eq2) = eqTyping (cong (REMatch _≈_ re1) eq1) p1 ,
                         eqTyping (cong (REMatch _≈_ re2) eq2) p2
match {_≈_ = _≈_} dec (reUnion re1 re2) str
        with match dec re1 str | match dec re2 str
... | yes p | _ = yes $ reMatchUnionLeft p
... | no _ | yes p = yes $ reMatchUnionRight p
... | no p1 | no p2 = no f where
    f : ¬ REMatch _≈_ (reUnion re1 re2) str
    f (reMatchUnionLeft ¬p1) = ⊥-elim $ p1 ¬p1
    f (reMatchUnionRight ¬p2) = ⊥-elim $ p2 ¬p2
match {A = A} {_≈_} dec (reSequence re) str =
    [ yes ∘ f (splits str) (concatInvSplits str) (splitsAllNonEmpty str)
        , no ∘ flip (anyYesAllNo ∘ g) ]′
            (anyYesOrAllNo seqdec (splits str)) where
    seqdec : (l : List (List A)) → Dec (All (REMatch _≈_ re) l)
    seqdec [] = yes []
    seqdec (x ∷ xs) with match dec re x | seqdec xs
    ... | yes p | yes ps = yes $ p ∷ ps
    ... | no ¬p | _ = no f where
        f : ¬ All (REMatch _≈_ re) (x ∷ xs)
        f (p ∷ _) = ¬p p
    ... | _ | no ¬p = no f where
        f : ¬ All (REMatch _≈_ re) (x ∷ xs)
        f (_ ∷ p) = ¬p p
    f : (l : List (List (List A))) →
        All (λ l' → concat l' ≡ str) l → All (All (λ l → ¬ ListEmpty l)) l →
        Any (All (REMatch _≈_ re)) l → REMatch _≈_ (reSequence re) str
    f [] [] [] ()
    f (x ∷ xs) (p ∷ ps) (p' ∷ ps') (here pm) =
        eqTyping (cong (REMatch _≈_ (reSequence re)) p) $ reMatchSequence pm p'
    f (x ∷ xs) (p ∷ ps) (p' ∷ ps') (there pm) = f xs ps ps' pm
    g : {str : List A} → REMatch _≈_ (reSequence re) str →
        Any (All (REMatch _≈_ re)) (splits str)
    g (reMatchSequence {strList = strList} p1 p2) =
        Data.List.Any.map
            (λ eq → eqTyping (cong (All (REMatch _≈_ re)) eq) p1)
            (splitsInvConcat strList p2)

