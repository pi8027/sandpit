Require Import
  Coq.Program.Program Omega Ssreflect.ssreflect Ssreflect.ssrnat Ssreflect.seq.

Set Implicit Arguments.

Ltac ssromega := rewrite ?NatTrec.trecE -?plusE -?minusE -?multE; omega.

Fixpoint fin (n : nat) : Set :=
  (if n is n.+1 then ()+fin n else Empty_set)%type.

Definition fin_case0 : forall (P : fin 0 -> Type) p, P p.
Proof.
  move=> P; case.
Defined.

Definition fin_caseS :
  forall P : forall n, fin n.+1 -> Type,
  (forall n, P n (inl ())) -> (forall n (p : fin n), P n (inr p)) ->
  forall n (p : fin n.+1), P n p.
Proof.
  move=> P H0 H1; case; simpl.
  - case; case; apply H0.
  - move=> n; case.
    - case; apply H0.
    - move=> p; apply H1.
Defined.

Definition fin_case :
  forall P : forall n : nat, fin n -> Type,
  (forall n, P n.+1 (inl ())) -> (forall n (p : fin n), P n.+1 (inr p)) ->
  forall n p, P n p.
Proof.
  by move=> P H0 H1; case; last move=> n //=; case; first case.
Defined.

Definition fin_rectS :
  forall P : forall n : nat, fin n.+1 -> Type,
  (forall n, P n (inl ())) -> (forall n p, P n p -> P n.+1 (inr p)) ->
  forall n p, P n p.
Proof.
  move=> P H0 H1; elim; simpl.
  - case; case; apply H0.
  - move=> n IHn; case.
    - case; apply H0.
    - by move=> p; apply H1.
Defined.

Definition fin_rect :
  forall P : forall n : nat, fin n -> Type,
  (forall n, P n.+1 (inl ())) -> (forall n p, P n p -> P n.+1 (inr p)) ->
  forall n p, P n p.
Proof.
  move=> P H0 H1; elim; first case.
  move=> n IH //=; elim; first case; auto.
Defined.

Definition fin2nat (n : nat) (a : fin n) : nat :=
  fin_rect (fun _ _ => nat) (fun _ => 0) (fun _ _ n => n.+1) n a.

Definition nat2fin : forall (n m : nat), fin m.+1.
Proof.
  elim.
  - by move=> m; apply inl.
  - simpl=> n IHn; case.
    - by apply inl.
    - move=> m; apply inr, IHn.
Defined.

Lemma fin2nat_range : forall n (a : fin n), lt (fin2nat n a) n.
Proof.
  apply fin_rect; simpl.
  - move=> n; ssromega.
  - move=> n p IH; ssromega.
Qed.

Lemma fin2nat_inv :
  forall n (a : fin n.+1), a = nat2fin (fin2nat n.+1 a) n.
Proof.
  apply fin_rectS.
  - done.
  - move=> n p H //=; f_equal; apply H.
Qed.

Definition fin_shift n m (a : fin n) : fin (n + m).
Proof.
  move: n a; apply fin_rect=> n //=.
  - by apply inl.
  - by move=> _ r; apply inr.
Defined.

Definition fin_plus n m (a : fin n) (b : fin m) : fin (n + m).-1.
Proof.
  move: n a; apply fin_rect=> n.
  - rewrite //= -/addn addnC.
    apply (fin_shift m n b).
  - case: n; first case.
    simpl=> n _ r; right; apply r.
Defined.

Lemma fin_shift_ident :
  forall n m (a : fin n), fin2nat n a = fin2nat (n + m) (fin_shift n m a).
Proof.
  move=> n m; move: n; apply fin_rect=> n; simpl.
  - done.
  - move=> a IHa; f_equal; apply IHa.
Qed.

Lemma fin_plus_is_plus :
  forall n m (a : fin n) (b : fin m),
  fin2nat n a + fin2nat m b = fin2nat (n + m).-1 (fin_plus n m a b).
Proof.
  move=> n m a b; move: n a; apply fin_rect=> n.
  - rewrite /addn //= -/addn /eq_rec_r /eq_rec /eq_rect.
    case (eq_sym (addnC n m)).
    apply fin_shift_ident.
  - rewrite {2}(lock fin_plus) //= -/addn; unlock.
    case: n; first case.
    by move=> n; rewrite /addn //= => p H; f_equal.
Qed.

Lemma eqmap_nat_fin :
  forall n m (a : fin n) (b : fin m),
  n = m -> fin2nat n a = fin2nat m b -> a ~= b.
Proof.
  move=> n m a; move: n a m.
  refine (fin_rect _ _ _)=> n.
  - refine (fin_case _ _ _)=> m; simpl.
    - by case => H _; rewrite H.
    - move=> b _ H; inversion H.
  - move=> a IHa; refine (fin_case _ _ _)=> m; simpl.
    - move=> _ H; inversion H.
    - move=> b; case=> H; case=> H0.
      by rewrite (IHa _ _ H H0).
Qed.

Lemma fin_plus_comm :
  forall n m (a : fin n) (b : fin m), fin_plus n m a b ~= fin_plus m n b a.
Proof.
  move=> n m a b; apply eqmap_nat_fin; first ssromega.
  rewrite -!fin_plus_is_plus; move: n a; apply fin_rect=> //= n a; ssromega.
Qed.

Fixpoint enumerate_fin n : seq (fin n) :=
  if n is n.+1
    then inl () :: map inr (enumerate_fin n)
    else [::].

Goal forall n v, foldr (fun v' p => v = v' \/ p) False (enumerate_fin n).
Proof.
  apply fin_rect; simpl.
  - by left.
  - move=> n v' IH; right; move: IH; elim (enumerate_fin n); simpl.
    - done.
    - move=> v vs IH; case.
      - by left; f_equal.
      - auto.
Qed.
