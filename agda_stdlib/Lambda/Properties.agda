
module Lambda.Properties where

open import Function
open import Algebra
open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Lambda.Core

+-comm = CommutativeSemiring.+-comm commutativeSemiring
+-assoc = CommutativeSemiring.+-assoc commutativeSemiring

≱⇒< : ∀ {n m} → ¬ n ≤ m → m < n
≱⇒< {zero} f = ⊥-elim $ f z≤n
≱⇒< {suc _} {zero} f = s≤s z≤n
≱⇒< {suc _} {suc _} f = s≤s $ ≱⇒< $ λ p → f $ s≤s p

<⇒≱ : ∀ {n m} → m < n → ¬ n ≤ m
<⇒≱ (s≤s p1) (s≤s p2) = <⇒≱ p1 p2

a-b+c≡a+c-b : ∀ {a b c} → b ≤ a → a ∸ b + c ≡ a + c ∸ b
a-b+c≡a+c-b z≤n = refl
a-b+c≡a+c-b {suc a} {suc b} {c} (s≤s p) = a-b+c≡a+c-b p

≤-addL : ∀ a {b c} → b ≤ c → a + b ≤ a + c
≤-addL zero p = p
≤-addL (suc a) p = s≤s (≤-addL a p)

≤-addL' : ∀ a {b c} → a ≤ c → b ≤ c ∸ a → a + b ≤ c
≤-addL' zero p1 p2 = p2
≤-addL' (suc a) {b} {zero} () p2
≤-addL' (suc a) {b} {suc n} (s≤s m≤n) p2 = s≤s $ ≤-addL' a m≤n p2

≤-addR : ∀ a {b c} → b ≤ c → b + a ≤ c + a
≤-addR a {b} {c} p rewrite +-comm b a | +-comm c a = ≤-addL a p

≤-addR' : ∀ a {b c} → a ≤ c → b ≤ c ∸ a → b + a ≤ c
≤-addR' a {b} {c} p1 p2 rewrite +-comm b a = ≤-addL' a p1 p2

≤-subL : ∀ a {b c} → a + b ≤ a + c → b ≤ c
≤-subL zero p = p
≤-subL (suc a) (s≤s p) = ≤-subL a p

≤-subL' : ∀ a {b c} → a + b ≤ c → b ≤ c ∸ a
≤-subL' zero p = p
≤-subL' (suc a) {zero} p = z≤n
≤-subL' (suc a) {suc b} {zero} ()
≤-subL' (suc a) {suc b} {suc c} (s≤s p) = ≤-subL' a p

≤-subR : ∀ a {b c} → b + a ≤ c + a → b ≤ c
≤-subR a {b} {c} p = ≤-subL a p' where
  p' : a + b ≤ a + c
  p' rewrite +-comm a b | +-comm a c = p

≤-subR' : ∀ a {b c} → b + a ≤ c → b ≤ c ∸ a
≤-subR' a {b} {c} p rewrite +-comm b a = ≤-subL' a p

≡-subL' : ∀ a {b c} → a + b ≡ c → b ≡ c ∸ a
≡-subL' zero p = p
≡-subL' (suc a) {zero} {zero} p = refl
≡-subL' (suc a) {suc b} {zero} ()
≡-subL' (suc a) {_} {suc n} p = ≡-subL' a $ cong pred p

≡-addL' : ∀ {a b c} → a ≤ c → b ≡ c ∸ a → a + b ≡ c
≡-addL' z≤n p2 = p2
≡-addL' {suc a} {b} {suc c} (s≤s p1) p2 = cong suc $ ≡-addL' p1 p2

shiftZero : ∀ c t → t ≡ shift 0 c t
shiftZero c (tvar n) with c ≤? n
...| yes p = cong tvar $ +-comm 0 n
...| no p = refl
shiftZero c (tapp t1 t2) = cong₂ tapp (shiftZero c t1) (shiftZero c t2)
shiftZero c (tabs t) = cong tabs (shiftZero (suc c) t)

shiftAdd : ∀ d d' c t → shift d c (shift d' c t) ≡ shift (d + d') c t
shiftAdd d d' c (tvar n) = r where
  open ≤-Reasoning
  r : shift d c (shift d' c (tvar n)) ≡ shift (d + d') c (tvar n)
  r with c ≤? n
  r | yes p1 with c ≤? (n + d')
  r | yes p1 | yes p2 rewrite +-assoc n d' d | +-comm d' d = refl
  r | yes p1 | no p2 = ⊥-elim $ p2 $
    begin c ≤⟨ p1 ⟩ n ≤⟨ m≤m+n n d' ⟩ n + d' ∎
  r | no p1 with c ≤? n
  r | no p1 | yes p2 = ⊥-elim $ p1 p2
  r | no p1 | no p2 = refl
shiftAdd d d' c (tapp t1 t2) = cong₂ tapp (shiftAdd d d' c t1) (shiftAdd d d' c t2)
shiftAdd d d' c (tabs t) = cong tabs (shiftAdd d d' (suc c) t)

nshiftFold : ∀ n t → nshift n t ≡ shift n 0 t
nshiftFold zero t = shiftZero 0 t
nshiftFold (suc n) t rewrite nshiftFold n t = shiftAdd 1 n 0 t

data Shifted : ℕ → ℕ → Term → Set where
  svar1 : ∀ {d c n} → n < c → Shifted d c (tvar n)
  svar2 : ∀ {d c n} → c + d ≤ n → d ≤ n → Shifted d c (tvar n)
  sapp : ∀ {d c t1 t2} → Shifted d c t1 → Shifted d c t2 → Shifted d c (tapp t1 t2)
  sabs : ∀ {d c t} → Shifted d (suc c) t → Shifted d c (tabs t)

weakShifted : ∀ {d c t} n → Shifted (d + n) c t → Shifted d (c + n) t
weakShifted {d} {c} zero p rewrite +-comm d 0 | +-comm c 0 = p
weakShifted {d} {c} {tvar n} (suc n') (svar1 p) =
  svar1 $ begin suc n ≤⟨ p ⟩ c ≤⟨ m≤m+n c (suc n') ⟩ c + suc n' ∎
  where open ≤-Reasoning
weakShifted {d} {c} {tvar n} (suc n') (svar2 p1 p2) =
  svar2 p1' $ begin d ≤⟨ m≤m+n d (suc n') ⟩ d + suc n' ≤⟨ p2 ⟩ n ∎
  where
  open ≤-Reasoning
  p1' : c + suc n' + d ≤ n
  p1' rewrite +-assoc c (suc n') d | +-comm (suc n') d = p1
weakShifted (suc n) (sapp p1 p2) = sapp (weakShifted (suc n) p1) (weakShifted (suc n) p2)
weakShifted (suc n) (sabs p) = sabs $ weakShifted (suc n) p

shiftShifted : ∀ d c t → Shifted d c (shift d c t)
shiftShifted d c (tvar n) with c ≤? n
...| no p = svar1 $ ≱⇒< p
...| yes p = svar2 (≤-addR d p) (n≤m+n n d)
shiftShifted d c (tapp t1 t2) = sapp (shiftShifted d c t1) (shiftShifted d c t2)
shiftShifted d c (tabs t) = sabs (shiftShifted d (suc c) t)

nshiftShifted : ∀ n t → Shifted n 0 (nshift n t)
nshiftShifted n t rewrite nshiftFold n t = shiftShifted n 0 t

betaShifted : ∀ n t1 t2 → Shifted 1 n (t1 [ n ≔ nshift (suc n) t2 ])
betaShifted n (tvar n') t2 with n ≟ n' | StrictTotalOrder.compare strictTotalOrder n n'
...| yes p | _ = weakShifted n $ nshiftShifted (suc n) t2
...| no p1 | tri< p2 _ _ =
  svar2 p2' $ begin 1 ≤⟨ s≤s z≤n ⟩ suc n ≤⟨ p2 ⟩ n' ∎
  where
  open ≤-Reasoning
  p2' : n + 1 ≤ n'
  p2' rewrite +-comm n 1 = p2
...| no p1 | tri≈ _ p2 _ = ⊥-elim $ p1 p2
...| no p1 | tri> _ _ p2 = svar1 p2
betaShifted n (tapp t1 t2) t3 = sapp (betaShifted n t1 t3) (betaShifted n t2 t3)
betaShifted n (tabs t1) t2 = sabs $ betaShifted (suc n) t1 t2

betaShifted' : ∀ n t1 t2 → Shifted 1 n (t1 [ n ≔ shift (suc n) 0 t2 ])
betaShifted' n t1 t2 rewrite sym (nshiftFold (suc n) t2) = betaShifted n t1 t2

substShiftedCancel :
  ∀ {d c n t1 t2} → c ≤ n → n < c + d → Shifted d c t1 → t1 ≡ t1 [ n ≔ t2 ]
substShiftedCancel {d} {c} {n} {tvar n'} {t2} p1 p2 p3 with n ≟ n' | p3
...| yes p4 | svar1 p5 rewrite p4  = ⊥-elim $ 1+n≰n $
  begin suc n' ≤⟨ p5 ⟩ c ≤⟨ p1 ⟩ n' ∎
  where open ≤-Reasoning
...| yes p4 | svar2 p5 p6 rewrite p4 = ⊥-elim $ 1+n≰n $
  begin suc c + d ≤⟨ s≤s p5 ⟩ suc n' ≤⟨ p2 ⟩ c + d ∎
  where open ≤-Reasoning
...| no p4 | _ = refl
substShiftedCancel p1 p2 (sapp p3 p4) =
  cong₂ tapp (substShiftedCancel p1 p2 p3) (substShiftedCancel p1 p2 p4)
substShiftedCancel p1 p2 (sabs p3) =
  cong tabs $ substShiftedCancel (s≤s p1) (s≤s p2) p3

shiftShiftSwap : ∀ d c d' c' → c ≤ c' → ∀ t →
            shift d c (shift d' c' t) ≡ shift d' (c' + d) (shift d c t)
shiftShiftSwap d c d' c' p (tvar n) = r where
  open ≤-Reasoning
  r : shift d c (shift d' c' (tvar n)) ≡ shift d' (c' + d) (shift d c (tvar n))
  r with c ≤? n | c' ≤? n
  r | yes p1 | yes p2 with c ≤? (n + d') | (c' + d) ≤? (n + d)
  r | yes p1 | yes p2 | yes p3 | yes p4
    rewrite +-assoc n d' d | +-assoc n d d' | +-comm d d' = refl
  r | yes p1 | yes p2 | _ | no p4 = ⊥-elim $ p4 $ ≤-addR d p2
  r | yes p1 | yes p2 | no p3 | _ = ⊥-elim $ p3 $
    begin c ≤⟨ p1 ⟩ n ≤⟨ m≤m+n n d' ⟩ n + d' ∎
  r | yes p1 | no p2 with c ≤? n | (c' + d) ≤? (n + d)
  r | yes p1 | no p2 | yes p3 | yes p4 = ⊥-elim $ p2 $ ≤-subR d p4
  r | yes p1 | no p2 | yes p3 | no p4 = refl
  r | yes p1 | no p2 | no p3 | _ = ⊥-elim $ p3 p1
  r | no p1 | yes p2 = ⊥-elim $ p1 $
    begin c ≤⟨ p ⟩ c' ≤⟨ p2 ⟩ n ∎
  r | no p1 | no p2 with c ≤? n | (c' + d) ≤? n
  r | no p1 | no p2 | yes p3 | _ = ⊥-elim $ p1 p3
  r | no p1 | no p2 | no p3 | yes p4 = ⊥-elim $ p2 $
    begin c' ≤⟨ m≤m+n c' d ⟩ c' + d ≤⟨ p4 ⟩ n ∎
  r | no p1 | no p2 | no p3 | no p4 = refl
shiftShiftSwap d c d' c' p (tapp t1 t2) =
  cong₂ tapp (shiftShiftSwap d c d' c' p t1) (shiftShiftSwap d c d' c' p t2)
shiftShiftSwap d c d' c' p (tabs t) =
  cong tabs (shiftShiftSwap d (suc c) d' (suc c') (s≤s p) t)

shiftUnshiftSwap : ∀ {d c d' c' t} → c' ≤ c → Shifted d' c' t →
              shift d c (unshift d' c' t) ≡ unshift d' c' (shift d (c + d') t)
shiftUnshiftSwap {d} {c} {d'} {c'} {tvar n} p1 p2 = r where
  open ≤-Reasoning
  r : shift d c (unshift d' c' (tvar n)) ≡ unshift d' c' (shift d (c + d') (tvar n))
  r with c' ≤? n | (c + d') ≤? n
  r | yes p3 | yes p4 with c' ≤? (n + d) | c ≤? (n ∸ d')
  r | yes p3 | yes p4 | yes p5 | yes p6 = cong tvar $ a-b+c≡a+c-b $
    begin d' ≤⟨ n≤m+n c d' ⟩ c + d' ≤⟨ p4 ⟩ n ∎
  r | yes p3 | yes p4 | yes p5 | no p6 = ⊥-elim $ p6 $ ≤-subR' d' p4
  r | yes p3 | yes p4 | no p5 | _ = ⊥-elim $ p5 $
    begin c' ≤⟨ p3 ⟩ n ≤⟨ m≤m+n n d ⟩ n + d ∎
  r | yes p3 | no p4 with c' ≤? n | c ≤? (n ∸ d') | p2
  r | yes p3 | no p4 | yes p5 | yes p6 | svar1 p7 = ⊥-elim $ 1+n≰n $
    begin suc n ≤⟨ p7 ⟩ c' ≤⟨ p3 ⟩ n ∎
  r | yes p3 | no p4 | yes p5 | yes p6 | svar2 p7 p8 = ⊥-elim $ p4 $ ≤-addR' d' p8 p6
  r | yes p3 | no p4 | yes p5 | no p6 | _ = refl
  r | yes p3 | no p4 | no p5 | _ | _ = ⊥-elim $ p5 p3
  r | no p3 | yes p4 with c ≤? n | c' ≤? (n + d)
  r | no p3 | yes p4 | yes p5 | yes p6 = ⊥-elim $ p3 $
    begin c' ≤⟨ p1 ⟩ c ≤⟨ p5 ⟩ n ∎
  r | no p3 | yes p4 | yes p5 | no p6 = refl
  r | no p3 | yes p4 | no p5 | _ = ⊥-elim $ p5 $
    begin c ≤⟨ m≤m+n c d' ⟩ c + d' ≤⟨ p4 ⟩ n ∎
  r | no p3 | no p4 with c' ≤? n | c ≤? n
  r | no p3 | no p4 | yes p5 | _ = ⊥-elim $ p3 p5
  r | no p3 | no p4 | no p5 | yes p6 = ⊥-elim $ p5 $
    begin c' ≤⟨ p1 ⟩ c ≤⟨ p6 ⟩ n ∎
  r | no p3 | no p4 | no p5 | no p6 = refl
shiftUnshiftSwap p1 (sapp p2 p3) =
  cong₂ tapp (shiftUnshiftSwap p1 p2) (shiftUnshiftSwap p1 p3)
shiftUnshiftSwap p1 (sabs p2) =
  cong tabs (shiftUnshiftSwap (s≤s p1) p2)

shiftSubstSwap :
  ∀ {d c n} → n < c → ∀ t1 t2 →
  shift d c (t1 [ n ≔ t2 ]) ≡ shift d c t1 [ n ≔ shift d c t2 ]
shiftSubstSwap {d} {c} {n} p (tvar n') t = r where
  open ≤-Reasoning
  r : shift d c (tvar n' [ n ≔ t ]) ≡ shift d c (tvar n') [ n ≔ shift d c t ]
  r with n ≟ n' | c ≤? n'
  r | yes p1 | yes p2 with n ≟ n' + d
  r | yes p1 | yes p2 | yes p3 = refl
  r | yes p1 | yes p2 | no p3 rewrite p1 = ⊥-elim $ 1+n≰n $
    begin suc n ≤⟨ p ⟩ c ≤⟨ p2 ⟩ n' ≡⟨ sym p1 ⟩ n ∎
  r | yes p1 | no p2 with n ≟ n'
  r | yes p1 | no p2 | yes p3 = refl
  r | yes p1 | no p2 | no p3 = ⊥-elim $ p3 p1
  r | no p1 | yes p2 with c ≤? n' | n ≟ n' + d
  r | no p1 | yes p2 | yes p3 | yes p4 = ⊥-elim $ 1+n≰n $ begin
    suc n' ≤⟨ m≤m+n (suc n') d ⟩
    suc n' + d ≡⟨ cong suc (sym p4) ⟩
    suc n ≤⟨ p ⟩
    c ≤⟨ p2 ⟩
    n' ∎
  r | no p1 | yes p2 | yes p3 | no p4 = refl
  r | no p1 | yes p2 | no p3 | _ = ⊥-elim $ p3 p2
  r | no p1 | no p2 with n ≟ n' | c ≤? n'
  r | no p1 | no p2 | yes p3 | _ = ⊥-elim $ p1 p3
  r | no p1 | no p2 | _ | yes p4 = ⊥-elim $ p2 p4
  r | no p1 | no p2 | no p3 | no p4 = refl
shiftSubstSwap p (tapp t1 t2) t3 =
  cong₂ tapp (shiftSubstSwap p t1 t3) (shiftSubstSwap p t2 t3)
shiftSubstSwap {d} {c} {n} p (tabs t1) t2
  rewrite shiftShiftSwap 1 0 d c z≤n t2 | +-comm c 1 =
  cong tabs $ shiftSubstSwap (s≤s p) t1 (shift 1 0 t2)

shiftSubstSwap' :
  ∀ {d c n} → c ≤ n → ∀ t1 t2 →
  shift d c (t1 [ n ≔ t2 ]) ≡ shift d c t1 [ n + d ≔ shift d c t2 ]
shiftSubstSwap' {d} {c} {n} p1 (tvar n') t = r where
  r : shift d c (tvar n' [ n ≔ t ]) ≡ shift d c (tvar n') [ n + d ≔ shift d c t ]
  r with n ≟ n' | c ≤? n'
  r | yes p2 | yes p3 with n + d ≟ n' + d
  r | yes p2 | yes p3 | yes p4 = refl
  r | yes p2 | yes p3 | no p4 = ⊥-elim $ p4 $ cong (λ n → n + d) p2
  r | yes p2 | no p3 rewrite sym p2 = ⊥-elim $ p3 p1
  r | no p2 | yes p3 with c ≤? n' | n + d ≟ n' + d
  r | no p2 | yes p3 | yes p4 | yes p5 = ⊥-elim $ p2 $ begin
    n ≡⟨ sym (m+n∸n≡m n d) ⟩
    n + d ∸ d ≡⟨ cong (λ n → n ∸ d) p5 ⟩
    n' + d ∸ d ≡⟨ m+n∸n≡m n' d ⟩
    n' ∎
    where open ≡-Reasoning
  r | no p2 | yes p3 | yes p4 | no p5 = refl
  r | no p2 | yes p3 | no p4 | _ = ⊥-elim $ p4 p3
  r | no p2 | no p3 with c ≤? n' | n + d ≟ n'
  r | no p2 | no p3 | yes p4 | _ = ⊥-elim $ p3 p4
  r | no p2 | no p3 | no p4 | yes p5 = ⊥-elim $ p3 $ begin
    c ≤⟨ p1 ⟩ n ≤⟨ m≤m+n n d ⟩ n + d ≡⟨ p5 ⟩ n' ∎
    where open ≤-Reasoning
  r | no p2 | no p3 | no p4 | no p5 = refl
shiftSubstSwap' p1 (tapp t1 t2) t3 =
  cong₂ tapp (shiftSubstSwap' p1 t1 t3) (shiftSubstSwap' p1 t2 t3)
shiftSubstSwap' {d} {c} {n} p1 (tabs t1) t2
  rewrite shiftShiftSwap 1 0 d c z≤n t2 | +-comm c 1 =
  cong tabs $ shiftSubstSwap' (s≤s p1) t1 (shift 1 0 t2)

unshiftShiftSetoff : ∀ {d c d' c'} t → c ≤ c' → c' ≤ d' + d + c →
                     unshift d' c' (shift (d' + d) c t) ≡ shift d c t
unshiftShiftSetoff {d} {c} {d'} {c'} (tvar n) p1 p2 = r where
  r : unshift d' c' (shift (d' + d) c (tvar n)) ≡ shift d c (tvar n)
  r with c ≤? n
  r | yes p3 with c' ≤? (n + (d' + d))
  r | yes p3 | yes p4 = cong tvar $ begin
    n + (d' + d) ∸ d' ≡⟨ cong (λ a → n + a ∸ d') (+-comm d' d) ⟩
    n + (d + d') ∸ d' ≡⟨ sym (cong (λ a → a ∸ d') (+-assoc n d d')) ⟩
    n + d + d' ∸ d' ≡⟨ m+n∸n≡m (n + d) d' ⟩
    n + d ∎
    where open ≡-Reasoning
  r | yes p3 | no p4 = ⊥-elim $ p4 $ begin
    c' ≤⟨ p2 ⟩
    d' + d + c ≤⟨ ≤-addL (d' + d) p3 ⟩
    d' + d + n ≡⟨ +-comm (d' + d) n ⟩
    n + (d' + d) ∎
    where open ≤-Reasoning
  r | no p3 with c' ≤? n
  r | no p3 | yes p4 = ⊥-elim $ p3 $
    begin c ≤⟨ p1 ⟩ c' ≤⟨ p4 ⟩ n ∎
    where open ≤-Reasoning
  r | no p3 | no p4 = refl
unshiftShiftSetoff (tapp t1 t2) p1 p2 =
  cong₂ tapp (unshiftShiftSetoff t1 p1 p2) (unshiftShiftSetoff t2 p1 p2)
unshiftShiftSetoff {d} {c} {d'} {c'} (tabs t) p1 p2 =
  cong tabs $ unshiftShiftSetoff t (s≤s p1) $ begin
    suc c' ≤⟨ s≤s p2 ⟩
    suc d' + d + c ≡⟨ cong suc (+-comm (d' + d) c) ⟩
    suc c + (d' + d) ≡⟨ +-comm (suc c) (d' + d) ⟩
    d' + d + suc c ∎
  where open ≤-Reasoning

unshiftSubstSwap :
  ∀ {c n} t1 t2 → c ≤ n → Shifted 1 c t1 →
  unshift 1 c (t1 [ suc n ≔ shift (suc c) 0 t2 ]) ≡
  unshift 1 c t1 [ n ≔ shift c 0 t2 ]
unshiftSubstSwap {c} {n} (tvar n') t2 p1 p2 = r where
  open ≤-Reasoning
  r : unshift 1 c (tvar n' [ suc n ≔ shift (suc c) 0 t2 ]) ≡
      unshift 1 c (tvar n') [ n ≔ shift c 0 t2 ]
  r with suc n ≟ n' | c ≤? n'
  r | yes p3 | yes p4 with n ≟ n' ∸ 1
  r | yes p3 | yes p4 | yes p5 = unshiftShiftSetoff t2 z≤n $
    begin c ≡⟨ +-comm 0 c ⟩ c + 0 ≤⟨ n≤1+n (c + 0) ⟩ suc (c + 0) ∎
  r | yes p3 | yes p4 | no p5 = ⊥-elim $ p5 $ ≡-subL' 1 p3
  r | yes p3 | no p4 with n ≟ n' | p2
  r | yes p3 | no p4 | yes p5 | _ = ⊥-elim $ 1+n≰n $
    begin suc n ≡⟨ p3 ⟩ n' ≡⟨ sym p5 ⟩ n ∎
  r | yes p3 | no p4 | no p5 | svar1 p6 = ⊥-elim $ 1+n≰n $
    begin suc n ≡⟨ p3 ⟩ n' ≤⟨ n≤1+n n' ⟩ suc n' ≤⟨ p6 ⟩ c ≤⟨ p1 ⟩ n ∎
  r | yes p3 | no p4 | no p5 | svar2 p6 p7 = ⊥-elim $ p4 $
    begin c ≤⟨ m≤m+n c 1 ⟩ c + 1 ≤⟨ p6 ⟩ n' ∎
  r | no p3 | yes p4 with c ≤? n' | n ≟ n' ∸ 1 | p2
  r | no p3 | yes p4 | yes p5 | yes p6 | svar1 p7 = ⊥-elim $ 1+n≰n $
    begin suc n' ≤⟨ p7 ⟩ c ≤⟨ p4 ⟩ n' ∎
  r | no p3 | yes p4 | yes p5 | yes p6 | svar2 p7 p8 = ⊥-elim $ p3 $ ≡-addL' p8 p6
  r | no p3 | yes p4 | yes p5 | no p6 | _ = refl
  r | no p3 | yes p4 | no p5 | _ | _ = ⊥-elim $ p5 p4
  r | no p3 | no p4 with c ≤? n' | n ≟ n'
  r | no p3 | no p4 | yes p5 | _ = ⊥-elim $ p4 p5
  r | no p3 | no p4 | no p5 | yes p6 = ⊥-elim $ p5 $
    begin c ≤⟨ p1 ⟩ n ≡⟨ p6 ⟩ n' ∎
  r | no p3 | no p4 | no p5 | no p6 = refl
unshiftSubstSwap (tapp t1 t2) t3 p1 (sapp p2 p3) =
  cong₂ tapp (unshiftSubstSwap t1 t3 p1 p2) (unshiftSubstSwap t2 t3 p1 p3)
unshiftSubstSwap {c} {n} (tabs t1) t2 p1 (sabs p2)
  rewrite shiftAdd 1 (suc c) 0 t2 | shiftAdd 1 c 0 t2 =
  cong tabs $ unshiftSubstSwap t1 t2 (s≤s p1) p2

substSubstSwap :
  ∀ n m t1 t2 t3 →
  t1 [ m ≔ shift (suc m) 0 t2 ] [ suc m + n ≔ shift (suc m) 0 t3 ] ≡
  t1 [ suc m + n ≔ shift (suc m) 0 t3 ] [ m ≔ shift (suc m) 0 (t2 [ n ≔ t3 ])]
substSubstSwap n m (tvar n') t2 t3 = r where
  r : tvar n' [ m ≔ shift (suc m) 0 t2 ] [ suc m + n ≔ shift (suc m) 0 t3 ] ≡
      tvar n' [ suc m + n ≔ shift (suc m) 0 t3 ] [ m ≔ shift (suc m) 0 (t2 [ n ≔ t3 ])]
  r with m ≟ n' | suc (m + n) ≟ n'
  r | yes p1 | yes p2 rewrite p1 = ⊥-elim $ m≢1+m+n n' $ sym p2
  r | yes p1 | no p2 with m ≟ n'
  r | yes p1 | no p2 | yes p3 rewrite +-comm (suc m) n =
    sym $ shiftSubstSwap' z≤n t2 t3
  r | yes p1 | no p2 | no p3 = ⊥-elim $ p3 p1
  r | no p1 | yes p2 with suc (m + n) ≟ n'
  r | no p1 | yes p2 | yes p3 =
    substShiftedCancel z≤n (≤′⇒≤ ≤′-refl) (shiftShifted (suc m) 0 t3)
  r | no p1 | yes p2 | no p3 = ⊥-elim $ p3 p2
  r | no p1 | no p2 with m ≟ n' | suc (m + n) ≟ n'
  r | no p1 | no p2 | yes p3 | _ = ⊥-elim $ p1 p3
  r | no p1 | no p2 | _ | yes p4 = ⊥-elim $ p2 p4
  r | no p1 | no p2 | no p3 | no p4 = refl
substSubstSwap n m (tapp t1l t1r) t2 t3 =
  cong₂ tapp (substSubstSwap n m t1l t2 t3) (substSubstSwap n m t1r t2 t3)
substSubstSwap n m (tabs t1) t2 t3 rewrite
    shiftAdd 1 (suc m) 0 t2 |
    shiftAdd 1 (suc m) 0 t3 |
    shiftAdd 1 (suc m) 0 (t2 [ n ≔ t3 ]) =
  cong tabs $ substSubstSwap n (suc m) t1 t2 t3

unshiftSubstSwap' :
  ∀ {n} t1 t2 → Shifted 1 0 t1 →
  unshift 1 0 (t1 [ suc n ≔ shift 1 0 t2 ]) ≡ unshift 1 0 t1 [ n ≔ t2 ]
unshiftSubstSwap' {n} t1 t2 p
  rewrite cong (λ t2 → unshift 1 0 t1 [ n ≔ t2 ]) (shiftZero 0 t2) =
  unshiftSubstSwap t1 t2 z≤n p

