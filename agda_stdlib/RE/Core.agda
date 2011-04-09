
{-# OPTIONS --universe-polymorphism #-}

module RE.Core where

open import Level
open import Function
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.List.All
open import Data.List.All.Properties
open import Data.List.Any
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

data ListEmpty {a} {A : Set a} : List A → Set a where
    listEmpty : ListEmpty []

data RE {a} (A : Set a) : Set a where
    reEmptySet : RE A            -- {}
    reEmptyString : RE A         -- {""}
    reSingleton : A → RE A       -- {character}
    reJoin : RE A → RE A → RE A  -- {xy | x ∈ L₁, y ∈ L₂}
    reUnion : RE A → RE A → RE A -- L₁ ∪ L₂
    reSequence : RE A → RE A     -- {""} ∪ {x | x ∈ L} ∪ {xx | x ∈ L} ∪ ...

data REMatch {a ℓ₁} {A : Set a} (_≈_ : Rel A ℓ₁) :
             REL (RE A) (List A) (a ⊔ ℓ₁) where
    reMatchEmptyString : REMatch _≈_ reEmptyString []
    reMatchSingleton : ∀ {c1 c2} → c1 ≈ c2 → REMatch _≈_ (reSingleton c1) [ c2 ]
    reMatchJoin : ∀ {re1 re2 s1 s2} → REMatch _≈_ re1 s1 → REMatch _≈_ re2 s2 →
                  REMatch _≈_ (reJoin re1 re2) (s1 ++ s2)
    reMatchUnionLeft : ∀ {re1 re2 str} →
                       REMatch _≈_ re1 str → REMatch _≈_ (reUnion re1 re2) str
    reMatchUnionRight : ∀ {re1 re2 str} →
                        REMatch _≈_ re2 str → REMatch _≈_ (reUnion re1 re2) str
    reMatchSequence :
        ∀ {re strList} →
        All (REMatch _≈_ re) strList → All (λ l → ¬ ListEmpty l) strList →
        REMatch _≈_ (reSequence re) (concat strList)

eqTyping : ∀ {t} {T1 T2 : Set t} → T1 ≡ T2 → T1 → T2
eqTyping refl a = a

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
    REMatch≈ = REMatch _≈_
    joindec : (s : List A × List A) →
           Dec (REMatch≈ re1 (proj₁ s) × REMatch≈ re2 (proj₂ s))
    joindec (ls , rs) with match dec re1 ls | match dec re2 rs
    ... | yes p1 | yes p2 = yes $ p1 , p2
    ... | no p | _ = no $ p ∘ proj₁
    ... | _ | no p = no $ p ∘ proj₂
    f : (l : List (List A × List A)) → All (λ s → str ≡ uncurry′ _++_ s) l →
        Any (λ s → REMatch≈ re1 (proj₁ s) × REMatch≈ re2 (proj₂ s)) l →
        REMatch≈ (reJoin re1 re2) str
    f [] _ ()
    f ((ls , rs) ∷ _) (p1 ∷ _) (here (p2 , p3)) = eqTyping
        (cong (REMatch≈ (reJoin re1 re2)) (sym p1)) (reMatchJoin p2 p3)
    f (_ ∷ xs) (_ ∷ p1) (there p2) = f xs p1 p2
    g : ∀ {ℓ} {re1 re2 : RE A} {_≈_ : Rel A ℓ} {str : List A} →
        REMatch _≈_ (reJoin re1 re2) str →
        Any (λ s → (REMatch _≈_ re1 (proj₁ s) × REMatch _≈_ re2 (proj₂ s))) (split str)
    g {ℓ} {re1} {re2} {_≈_} (reMatchJoin {s1 = s1} {s2} p1 p2) =
        Data.List.Any.map g' $ splitInvAppend s1 s2 where
        g' : {x : List A × List A} →
             (s1 ≡ proj₁ x) × (s2 ≡ proj₂ x) →
             REMatch _≈_ re1 (proj₁ x) × REMatch _≈_ re2 (proj₂ x)
        g' {x} (eq1 , eq2) = eqTyping (cong (REMatch _≈_ re1) eq1) p1 ,
                             eqTyping (cong (REMatch _≈_ re2) eq2) p2
match {_≈_ = _≈_} dec (reUnion re1 re2) str
        with match dec re1 str | match dec re2 str
... | yes p | _ = yes $ reMatchUnionLeft p
... | no _ | yes p = yes $ reMatchUnionRight p
... | no p1 | no p2 = no f where
    f : ¬ REMatch _≈_ (reUnion re1 re2) str
    f (reMatchUnionLeft ¬p1) = ⊥-elim $ p1 ¬p1
    f (reMatchUnionRight ¬p2) = ⊥-elim $ p2 ¬p2
match dec (reSequence re) str = {!!}


