Require Import
  Coq.Program.Program Omega Ssreflect.ssreflect Ssreflect.ssrnat Ssreflect.seq.

Set Implicit Arguments.

Ltac ssromega := rewrite ?NatTrec.trecE -?plusE -?minusE -?multE; omega.

Fixpoint t (n : nat) : Set :=
  (if n is n.+1 then option (t n) else Empty_set)%type.

Definition rect_case0 : forall (P : t 0 -> Type) p, P p.
Proof.
  move=> P; case.
Defined.

Definition rect_caseS :
  forall P : forall n, t n.+1 -> Type,
  (forall n, P n None) -> (forall n (p : t n), P n (Some p)) ->
  forall n (p : t n.+1), P n p.
Proof.
  move=> P H0 H1; case; simpl.
  - case; [case | apply H0].
  - move=> n; case.
    - move=> p; apply H1.
    - apply H0.
Defined.

Definition rect_case :
  forall P : forall n : nat, t n -> Type,
  (forall n, P n.+1 None) -> (forall n (p : t n), P n.+1 (Some p)) ->
  forall n p, P n p.
Proof.
  by move=> P H0 H1; case; last move=> n //=; case.
Defined.

Definition rectS :
  forall P : forall n : nat, t n.+1 -> Type,
  (forall n, P n None) -> (forall n p, P n p -> P n.+1 (Some p)) ->
  forall n p, P n p.
Proof.
  move=> P H0 H1; elim; simpl.
  - case; [case | apply H0].
  - move=> n IHn; case.
    - by move=> p; apply H1.
    - apply H0.
Defined.

Definition rect :
  forall P : forall n : nat, t n -> Type,
  (forall n, P n.+1 None) -> (forall n p, P n p -> P n.+1 (Some p)) ->
  forall n p, P n p.
Proof.
  move=> P H0 H1; elim; first case.
  move=> n IH //=; case; auto.
Defined.

Definition to_nat (n : nat) (a : t n) : nat :=
  rect (fun _ _ => nat) (fun _ => 0) (fun _ _ n => n.+1) n a.

Definition of_nat : forall (n m : nat), t m.+1.
Proof.
  elim.
  - by move=> m; apply None.
  - simpl=> n IHn; case.
    - by apply None.
    - move=> m; apply Some, IHn.
Defined.

Lemma to_nat_range : forall n a, lt (to_nat n a) n.
Proof.
  apply rect => //= [n | n p IH]; ssromega.
Qed.

Lemma to_nat_of_nat_inv : forall n a, a = of_nat (to_nat n.+1 a) n.
Proof.
  by apply rectS=> //= n p H; f_equal.
Qed.

Lemma to_nat_eq_conserve :
  forall n m a b, n = m -> (a ~= b <-> to_nat n a = to_nat m b).
Proof.
  move=> n m a b H; split.
  - by move: b; rewrite -H=> b H0; f_equal; apply JMeq_eq.
  - move: n a m b H; refine (rect _ _ _)=> n.
    - by refine (rect_case _ _ _)=> //= m; case=> H _; rewrite H.
    - move=> a IHa; refine (rect_case _ _ _)=> m //= b.
      by case=> H; case=> H0; rewrite (IHa _ _ H H0).
Qed.

Definition L n m (a : t n) : t (n + m).
Proof.
  move: n a; apply rect=> n //=.
  - by apply None.
  - by move=> _ r; apply Some.
Defined.

Fixpoint R n m (a : t n) : t (m + n) :=
  match m with
    | 0 => a
    | S m => Some (R n m a)
  end.

Definition plus n m (a : t n) (b : t m) : t (n + m).-1.
Proof.
  move: n a; apply rect=> n.
  - rewrite //= -/addn addnC.
    apply (L m n b).
  - case: n; first case.
    simpl=> n _ r; apply Some; apply r.
Defined.

Lemma L_sanity : forall n m a, to_nat n a = to_nat (n + m) (L n m a).
Proof.
  move=> n m; move: n; apply rect=> //= n a IHa; f_equal; apply IHa.
Qed.

Lemma R_sanity : forall n m a, m + to_nat n a = to_nat (m + n) (R n m a).
Proof.
  by move=> n; elim=> //= m IHm a; rewrite /addn //=; f_equal.
Qed.

Lemma plus_to_nat_distr :
  forall n m a b, to_nat n a + to_nat m b = to_nat (n + m).-1 (plus n m a b).
Proof.
  move=> n m a b; move: n a; apply rect=> n.
  - rewrite /addn //= -/addn /eq_rec_r /eq_rec /eq_rect.
    case (eq_sym (addnC n m)); apply L_sanity.
  - rewrite {2}(lock plus) //= -/addn; unlock.
    case: n; first case.
    by move=> n; rewrite /addn => //= p H; f_equal.
Qed.

Lemma plus_comm : forall n m a b, plus n m a b ~= plus m n b a.
Proof.
  move=> n m a b; rewrite to_nat_eq_conserve; last ssromega.
  rewrite -!plus_to_nat_distr; move: n a; apply rect=> //= n a; ssromega.
Qed.

Fixpoint enumerate_fin n : seq (t n) :=
  if n is n.+1
    then None :: map Some (enumerate_fin n)
    else [::].

Goal forall n v, foldr (fun v' p => v = v' \/ p) False (enumerate_fin n).
Proof.
  apply rect=> //= n.
  - by left.
  - move=> v' IH; right; move: IH.
    elim (enumerate_fin n)=> //= v vs IH; case.
    - by left; f_equal.
    - auto.
Qed.
