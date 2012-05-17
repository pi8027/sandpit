
Require Import Arith.
Require Import Arith.Euclid.
Require Import Arith.Wf_nat.
Require Import Omega.

Definition sq1 (n : nat) : nat := n * n.

Definition sq2 (a n : nat) : nat := a * (n * n).

Fixpoint pow1 (a b : nat) : nat :=
  match b with
  | 0 => 1
  | S b' => pow1 a b' * a
  end.

Lemma pow2 (a b : nat) : nat.
  induction b as [b IH] using lt_wf_rec.
  assert (diveucl b 2).
  exact (eucl_dev 2 (le_S 1 1 (le_n 1)) b).
  destruct H.
  destruct r.
  destruct q.
  exact 1.
  apply sq1.
  apply (IH (S q)).
  omega.
  apply (sq2 a).
  apply (IH q).
  omega.
Defined.

Theorem pow_equivalence : forall (a b : nat), pow1 a b = pow2 a b.
  intros.
  induction b as [b IH] using lt_wf_rec.
  assert (diveucl b 2).
  assert (0 < 2).
  omega.
  exact (eucl_dev 2 H b).
  destruct H.
  destruct r.
  destruct q.
  rewrite e.
  unfold mult, plus, pow1, pow2.

