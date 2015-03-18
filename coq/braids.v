Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Printing Width 100.

Axiom (Braid : nat -> Set).
Axiom (sigma : forall n m : nat, m < n -> Braid n).
Axiom (empty : forall n, Braid n).
Axiom (residual : forall n, Braid n -> Braid n -> Braid n).
Axiom (comp : forall n, Braid n -> Braid n -> Braid n).

Delimit Scope braid_scope with braid.

Notation σ n m := (@sigma n m (@erefl _ _)) (only parsing).
Notation σ' m := (@sigma _ m (@erefl _ _)).
Notation "1" := (@empty _) : braid_scope.
Notation "x / y" := (residual x y) (at level 40, left associativity) : braid_scope.
Notation "x ∘ y" := (comp x y) (at level 25, left associativity) : braid_scope.

Axiom (compA :   (forall n (x y z : Braid n), x ∘ y ∘ z = x ∘ (y ∘ z))%braid).

Axiom (resxx :   (forall n (x : Braid n), x / x = 1)%braid).
Axiom (resx1 :   (forall n (x : Braid n), x / 1 = x)%braid).
Axiom (res1x :   (forall n (x : Braid n), 1 / x = 1)%braid).
Axiom (cube :    (forall n (x y z : Braid n), (x / y) / (z / y) = (x / z) / (y / z))%braid).
Axiom (compx1 :  (forall n (x : Braid n), x ∘ 1 = x)%braid).
Axiom (comp1x :  (forall n (x : Braid n), 1 ∘ x = x)%braid).
Axiom (resxc :   (forall n (x y z : Braid n), x / (y ∘ z) = x / y / z)%braid).
Axiom (rescx :   (forall n (x y z : Braid n), (x ∘ y) / z = (x / z) ∘ (y / (z / x)))%braid).

Axiom (ressig1 : (forall n a b (Ha : a < n) (Hb : b < n),
                  2 <= (a - b) + (b - a) -> sigma Ha / sigma Hb = sigma Ha)%braid).
Axiom (ressig2 : (forall n a b (Ha : a < n) (Hb : b < n),
                  (a - b) + (b - a) = 1%nat -> sigma Ha / sigma Hb = sigma Ha ∘ sigma Hb)%braid).

Goal (σ 6 3 ∘ σ 6 2 ∘ σ 6 1 / σ 6 1 ∘ σ 6 0 ∘ σ 6 3 ∘ σ 6 2 ∘ σ 6 4 = σ 6 1 ∘ σ 6 0)%braid.
Proof.
  do ! ((rewrite !(rescx, resxc, resxx, res1x, resx1, compx1, comp1x)) ||
        (rewrite ressig1; last by []) ||
        (rewrite ressig2; last by [])).
  done.
Qed.
