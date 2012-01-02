
module Lambda.DeBruijn.Confluence where

open import Function
open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Lambda.DeBruijn.Core
open import Lambda.DeBruijn.Properties

rtcTrans : ∀ {ℓ} {A : Set ℓ} {rel : Rel A ℓ} {a b c : A} →
           rtclosure rel a b → rtclosure rel b c → rtclosure rel a c
rtcTrans rtc0 r2 = r2
rtcTrans (rtcs r1 r2) r3 = rtcs r1 (rtcTrans r2 r3)

→β*appl : ∀ {t1 t1' t2} → t1 →β* t1' → tapp t1 t2 →β* tapp t1' t2
→β*appl rtc0 = rtc0
→β*appl (rtcs r1 r2) = rtcs (→βappl r1) (→β*appl r2)

→β*appr : ∀ {t1 t2 t2'} → t2 →β* t2' → tapp t1 t2 →β* tapp t1 t2'
→β*appr rtc0 = rtc0
→β*appr (rtcs r1 r2) = rtcs (→βappr r1) (→β*appr r2)

→β*abs : ∀ {t t'} → t →β* t' → tabs t →β* tabs t'
→β*abs rtc0 = rtc0
→β*abs (rtcs r1 r2) = rtcs (→βabs r1) (→β*abs r2)

parRefl : ∀ {t} → t →βP t
parRefl {tvar _} = →βPvar
parRefl {tapp _ _} = →βPapp parRefl parRefl
parRefl {tabs _} = →βPabs parRefl

→β⊂→βP : ∀ {t t'} → t →β t' → t →βP t'
→β⊂→βP →βbeta = →βPbeta parRefl parRefl
→β⊂→βP (→βappl r) = →βPapp (→β⊂→βP r) parRefl
→β⊂→βP (→βappr r) = →βPapp parRefl (→β⊂→βP r)
→β⊂→βP (→βabs r) = →βPabs (→β⊂→βP r)

→βP⊂→β* : ∀ {t t'} → t →βP t' → t →β* t'
→βP⊂→β* →βPvar = rtc0
→βP⊂→β* (→βPapp r1 r2) = rtcTrans (→β*appl (→βP⊂→β* r1)) (→β*appr (→βP⊂→β* r2))
→βP⊂→β* (→βPabs r) = →β*abs (→βP⊂→β* r)
→βP⊂→β* (→βPbeta r1 r2) =
  rtcTrans
    (→β*appl (→β*abs (→βP⊂→β* r1)))
    (rtcTrans (→β*appr (→βP⊂→β* r2)) (rtcs →βbeta rtc0))

shiftConservation→β : ∀ {d c t1 t2} → t1 →β t2 → Shifted d c t1 → Shifted d c t2
shiftConservation→β {d} {c} {tapp (tabs t1) t2} →βbeta (sapp (sabs s1) s2) =
  betaShifted2 s1 s2
shiftConservation→β (→βappl p) (sapp s1 s2) = sapp (shiftConservation→β p s1) s2
shiftConservation→β (→βappr p) (sapp s1 s2) = sapp s1 (shiftConservation→β p s2)
shiftConservation→β (→βabs p) (sabs s1) = sabs (shiftConservation→β p s1)

shiftConservation→β* : ∀ {d c t1 t2} → t1 →β* t2 → Shifted d c t1 → Shifted d c t2
shiftConservation→β* rtc0 s = s
shiftConservation→β* (rtcs p1 p2) s = shiftConservation→β* p2 (shiftConservation→β p1 s)

shiftConservation→βP : ∀ {d c t1 t2} → t1 →βP t2 → Shifted d c t1 → Shifted d c t2
shiftConservation→βP p s = shiftConservation→β* (→βP⊂→β* p) s

unshiftShiftSwap :
  ∀ {d c d' c' t} → c' ≤ c → Shifted d c t →
  shift d' c' (unshift d c t) ≡ unshift d (c + d') (shift d' c' t)
unshiftShiftSwap {d} {c} {d'} {c'} {tvar n} p s1 = r where
  open ≤-Reasoning
  r : shift d' c' (unshift d c (tvar n)) ≡ unshift d (c + d') (shift d' c' (tvar n))
  r with c ≤? n | c' ≤? n
  r | yes p1 | yes p2 with c' ≤? (n ∸ d) | (c + d') ≤? (n + d') | s1
  r | yes p1 | yes p2 | _ | _ | svar1 p5 =
    ⊥-elim $ 1+n≰n $ begin suc n ≤⟨ p5 ⟩ c ≤⟨ p1 ⟩ n ∎
  r | yes p1 | yes p2 | yes p3 | yes p4 | svar2 p5 p6 =
    cong tvar $ sym $ a+b∸c≡a∸c+b n d' d p6
  r | yes p1 | yes p2 | no p3 | yes p4 | svar2 p5 p6 = ⊥-elim $ p3 $
    begin c' ≤⟨ p ⟩ c ≤⟨ ≤-subR' d p5 ⟩ n ∸ d ∎
  r | yes p1 | yes p2 | _ | no p4 | _ = ⊥-elim $ p4 $ ≤-addR d' p1
  r | yes p1 | no p2 = ⊥-elim $ p2 $ begin c' ≤⟨ p ⟩ c ≤⟨ p1 ⟩ n ∎
  r | no p1 | yes p2 with c' ≤? n | (c + d') ≤? (n + d')
  r | no p1 | yes p2 | yes _ | yes p3 = ⊥-elim $ p1 $ ≤-subR d' p3
  r | no p1 | yes p2 | yes _ | no p3 = refl
  r | no p1 | yes p2 | no p3 | _ = ⊥-elim $ p3 p2
  r | no p1 | no p2 with c' ≤? n | (c + d') ≤? n
  r | no p1 | no p2 | _ | yes p4 =
    ⊥-elim $ p1 $ begin c ≤⟨ m≤m+n c d' ⟩ c + d' ≤⟨ p4 ⟩ n ∎
  r | no p1 | no p2 | yes p3 | no p4 = ⊥-elim $ p2 p3
  r | no p1 | no p2 | no p3 | no p4 = refl
unshiftShiftSwap p (sapp s1 s2) =
  cong₂ tapp (unshiftShiftSwap p s1) (unshiftShiftSwap p s2)
unshiftShiftSwap p (sabs s1) = cong tabs (unshiftShiftSwap (s≤s p) s1)

shiftLemma : ∀ {t t' d c} → t →βP t' → shift d c t →βP shift d c t'
shiftLemma →βPvar = parRefl
shiftLemma (→βPapp r1 r2) = →βPapp (shiftLemma r1) (shiftLemma r2)
shiftLemma (→βPabs r) = →βPabs (shiftLemma r)
shiftLemma {d = d} {c} (→βPbeta {t1} {t1'} {t2} {t2'} r1 r2) = r where
  open ≡-Reasoning
  eq : shift d c (unshift 1 0 (t1' [ 0 ≔ shift 1 0 t2' ])) ≡
       unshift 1 0 (shift d (suc c) t1' [ 0 ≔ shift 1 0 (shift d c t2') ])
  eq = begin
    shift d c (unshift 1 0 (t1' [ 0 ≔ shift 1 0 t2' ]))
      ≡⟨ shiftUnshiftSwap z≤n (betaShifted' 0 t1' t2') ⟩
    unshift 1 0 (shift d (c + 1) (t1' [ 0 ≔ shift 1 0 t2' ]))
      ≡⟨ cong (unshift 1 0) $ begin
        shift d (c + 1) (t1' [ 0 ≔ shift 1 0 t2' ])
          ≡⟨ cong (λ c → shift d c (t1' [ 0 ≔ shift 1 0 t2' ])) (+-comm c 1) ⟩
        shift d (suc c) (t1' [ 0 ≔ shift 1 0 t2' ])
          ≡⟨ shiftSubstSwap (m≤m+n 1 c) t1' (shift 1 0 t2') ⟩
        shift d (suc c) t1' [ 0 ≔ shift d (suc c) (shift 1 0 t2') ]
          ≡⟨ cong (λ t → shift d (suc c) t1' [ 0 ≔ t ]) $ begin
            shift d (suc c) (shift 1 0 t2')
              ≡⟨ cong (λ c → shift d c (shift 1 0 t2')) (+-comm 1 c) ⟩
            shift d (c + 1) (shift 1 0 t2')
              ≡⟨ sym (shiftShiftSwap 1 0 d c t2' z≤n) ⟩
            shift 1 0 (shift d c t2') ∎
          ⟩
        shift d (suc c) t1' [ 0 ≔ shift 1 0 (shift d c t2') ] ∎
      ⟩
    unshift 1 0 (shift d (suc c) t1' [ 0 ≔ shift 1 0 (shift d c t2') ]) ∎
  r : shift d c (tapp (tabs t1) t2) →βP
      shift d c (unshift 1 0 (t1' [ 0 ≔ shift 1 0 t2' ]))
  r rewrite eq = →βPbeta (shiftLemma r1) (shiftLemma r2)

unshiftLemma : ∀ {t t' d c} → t →βP t' → Shifted d c t → unshift d c t →βP unshift d c t'
unshiftLemma →βPvar _ = parRefl
unshiftLemma (→βPapp r1 r2) (sapp s1 s2) = →βPapp (unshiftLemma r1 s1) (unshiftLemma r2 s2)
unshiftLemma (→βPabs r) (sabs s) = →βPabs (unshiftLemma r s)
unshiftLemma {d = d} {c} (→βPbeta {t1} {t1'} {t2} {t2'} r1 r2) (sapp (sabs s1) s2) = r where
  open ≡-Reasoning
  eq : unshift d c (unshift 1 0 (t1' [ 0 ≔ shift 1 0 t2' ])) ≡
       unshift 1 0 (unshift d (suc c) t1' [ 0 ≔ shift 1 0 (unshift d c t2') ])
  eq = begin
    unshift d c (unshift 1 0 (t1' [ 0 ≔ shift 1 0 t2' ]))
      ≡⟨ unshiftUnshiftSwap z≤n (betaShifted' 0 t1' t2')
        (betaShifted2 (shiftConservation→βP r1 s1) (shiftConservation→βP r2 s2)) ⟩
    unshift 1 0 (unshift d (c + 1) (t1' [ 0 ≔ shift 1 0 t2' ]))
      ≡⟨ cong (unshift 1 0) $ begin
        unshift d (c + 1) (t1' [ 0 ≔ shift 1 0 t2' ])
          ≡⟨ cong (λ c → unshift d c (t1' [ 0 ≔ shift 1 0 t2' ])) (+-comm c 1) ⟩
        unshift d (suc c) (t1' [ 0 ≔ shift 1 0 t2' ])
          ≡⟨ {!!} ⟩
        unshift d (suc c) t1' [ 0 ≔ unshift d (suc c) (shift 1 0 t2') ]
          ≡⟨ cong (λ t → unshift d (suc c) t1' [ 0 ≔ t ]) $ begin
            unshift d (suc c) (shift 1 0 t2')
              ≡⟨ cong (λ c → unshift d c (shift 1 0 t2')) (+-comm 1 c) ⟩
            unshift d (c + 1) (shift 1 0 t2')
              ≡⟨ sym (unshiftShiftSwap z≤n (shiftConservation→βP r2 s2)) ⟩
            shift 1 0 (unshift d c t2') ∎
          ⟩
        unshift d (suc c) t1' [ 0 ≔ shift 1 0 (unshift d c t2') ] ∎
      ⟩
    unshift 1 0 (unshift d (suc c) t1' [ 0 ≔ shift 1 0 (unshift d c t2') ]) ∎
  r : tapp (tabs (unshift d (suc c) t1)) (unshift d c t2) →βP
      unshift d c (unshift 1 0 (t1' [ 0 ≔ shift 1 0 t2' ]))
  r rewrite eq = →βPbeta (unshiftLemma r1 s1) (unshiftLemma r2 s2)

substLemma : ∀ {n t1 t1' t2 t2'} →
             t1 →βP t1' → t2 →βP t2' → t1 [ n ≔ t2 ] →βP t1' [ n ≔ t2' ]
substLemma {n} {tvar n'} →βPvar r1 with n ≟ n'
...| yes p = r1
...| no p = →βPvar
substLemma (→βPapp r1 r2) r3 = →βPapp (substLemma r1 r3) (substLemma r2 r3)
substLemma (→βPabs r1) r2 = →βPabs $ substLemma r1 $ shiftLemma r2
substLemma {n} {t2 = t3} {t3'} (→βPbeta {t1} {t1'} {t2} {t2'} r1 r2) r3 = r where
  open ≡-Reasoning
  eq : unshift 1 0 (t1' [ 0 ≔ shift 1 0 t2' ]) [ n ≔ t3' ] ≡
       unshift 1 0 ((t1' [ suc n ≔ shift 1 0 t3' ]) [ 0 ≔ shift 1 0 (t2' [ n ≔ t3' ]) ])
  eq = begin
    unshift 1 0 (t1' [ 0 ≔ shift 1 0 t2' ]) [ n ≔ t3' ]
      ≡⟨ sym (unshiftSubstSwap' (t1' [ 0 ≔ shift 1 0 t2' ]) t3' (betaShifted' 0 t1' t2')) ⟩
    unshift 1 0 (t1' [ 0 ≔ shift 1 0 t2' ] [ suc n ≔ shift 1 0 t3' ])
      ≡⟨ cong (unshift 1 0) (substSubstSwap n 0 t1' t2' t3') ⟩
    unshift 1 0 ((t1' [ suc n ≔ shift 1 0 t3' ]) [ 0 ≔ shift 1 0 (t2' [ n ≔ t3' ]) ]) ∎
  r : tapp (tabs (t1 [ suc n ≔ shift 1 0 t3 ])) (t2 [ n ≔ t3 ]) →βP
      (unshift 1 0 (t1' [ 0 ≔ shift 1 0 t2' ])) [ n ≔ t3' ]
  r rewrite eq = →βPbeta (substLemma r1 (shiftLemma r3)) (substLemma r2 r3)

starLemma : ∀ {t t'} → t →βP t' → t' →βP t *
starLemma →βPvar = →βPvar
starLemma {tapp (tvar n) t2} (→βPapp p1 p2) =
  →βPapp (starLemma p1) (starLemma p2)
starLemma {tapp (tapp t1l t1r) t2} (→βPapp p1 p2) =
  →βPapp (starLemma p1) (starLemma p2)
starLemma {tapp (tabs t1) t2} {tapp (tvar _) t2'} (→βPapp () p2)
starLemma {tapp (tabs t1) t2} {tapp (tapp _ _) t2'} (→βPapp () p2)
starLemma {tapp (tabs t1) t2} {tapp (tabs t1') t2'} (→βPapp (→βPabs p1) p2) =
  →βPbeta (starLemma p1) (starLemma p2)
starLemma (→βPabs p1) = →βPabs (starLemma p1)
starLemma {tapp (tabs t1) t2} (→βPbeta {.t1} {t1'} {.t2} {t2'} p1 p2) =
  unshiftLemma
    (substLemma (starLemma p1) (shiftLemma (starLemma p2)))
    (betaShifted 0 t1' t2')
