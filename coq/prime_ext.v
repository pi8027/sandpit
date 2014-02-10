(*
(add-to-list 'coq-load-path "/home/i/src/coq/regular/")
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype div bigop prime.

Lemma primeP' p :
  reflect (1 < p /\ forall p', p' < p -> prime p' -> ~ p' %| p) (prime p).
Proof.
  case/boolP: (prime p) => H; constructor; [split | case].
  - by move: p H; do 2 case => //.
  - case/primeP: H => H H0 p' H1 H2; case/(H0 p')/orP.
    + by move: p' H2 {H1}; do 2 case => //.
    + by rewrite (ltn_eqF H1).
  - move => H0 H1; move: H; apply/negP/negPn/primeP; split => // d H.
    apply/negP; move/negP; rewrite negb_or; case/andP => H2 H3.
    have {H2} H2: 1 < d by
      case: d H H2 H3 => //; [rewrite dvd0n eq_sym => -> | case].
    have {H3} H3: d < p by
      move: (dvdn_leq (ltnW H0) H) H3; rewrite leq_eqVlt; case/orP => // ->.
    apply (H1 (pdiv d)).
    + by apply leq_ltn_trans with d => //; apply pdiv_leq, ltnW.
    + by apply pdiv_prime.
    + by apply dvdn_trans with d => //; apply pdiv_dvd.
Qed.

Fixpoint search_prime n m :=
  if prime n
    then n
    else if m is m.+1
      then search_prime n.+1 m
      else 0.

Definition next_prime n :=
  search_prime n (n.+1 * \prod_(0 <= p < n.+1 | prime p) p).+1.

Lemma next_prime_is_prime n : prime (next_prime n).
Proof.
  suff: next_prime n != 0 by
    rewrite /next_prime; move: _.+1 => m;
      elim: m n => /= [| m IH] n; case: ifP => //= _; apply IH.
  rewrite /next_prime; apply/negP => H.
  have {H} H p :
      n <= p <= (n.+1 * \prod_(0 <= p < n.+1 | prime p) p).+1 + n -> ~~ prime p.
    move: H; move: _.+1 => m.
    elim: m n => /= [| m IH] n.
    - by rewrite add0n -eqn_leq => H; move/eqP => <-;
        apply/negP => H0; move: H; rewrite H0 /=; case: n H0.
    - case: ifP; first by case: n.
      move => H; move/IH => {IH} H0; rewrite leq_eqVlt; case/andP; case/orP.
      + by move/eqP => <-; rewrite H.
      + by move => H1 H2; apply H0; rewrite H1 /= -addSnnS.
  suff: prime (n.+1 * \prod_(0 <= p < n.+1 | prime p) p).+1.
    apply/negP/H; rewrite leq_addr andbT {H}; apply leqW.
    apply leq_trans with (n.+1 * 1); first by rewrite muln1.
    by rewrite leq_mul2l /=;apply big_ind => //=; case => // ?; case.
  apply/primeP'; split.
  - by rewrite ltnS muln_gt0 /=; apply big_ind => //; case => // ?; case.
  - move => p'; rewrite ltnS => H0 H1 H2; case (leqP p' n) => H3.
    + move: H2; rewrite -addn1 dvdn_addr;
        first by rewrite dvdn1; move/eqP => ?; subst p'; move: H1.
      apply dvdn_mull.
      rewrite big_mkord -(subnKC (leqW H3)) big_split_ord /=; apply dvdn_mull.
      suff: p' %| \prod_(0 <= i < n.+1 - p' | prime (p' + i)) (p' + i)
        by rewrite big_mkord.
      by rewrite /index_iota subn0 subSn //= big_cons addn0 H1; apply dvdn_mulr.
    + by move: (H p'); rewrite (ltnW H3) /=;
        move/(_ (leq_trans (leqW H0) (leq_addr _ _)))/negP; apply.
Qed.

Lemma next_prime_smallest n p : n <= p < next_prime n -> ~~ prime p.
Proof.
  move: (next_prime_is_prime n).
  rewrite /next_prime; move: _.+1 => m.
  elim: m n => //= [| m IH] n; case: ifP => //=;
    try by move => _ _; case/andP;
           rewrite -ltnS => H; move/(leq_trans H); rewrite ltnn.
  move => H; move/IH => H0; rewrite leq_eqVlt; case/andP; case/orP.
  - by move/eqP => <- _; rewrite H.
  - by move => H1 H2; apply H0; rewrite H1.
Qed.

Lemma next_prime_spec3 n : n <= next_prime n.
Proof.
  by move: (next_prime_is_prime n); rewrite /next_prime;
    move: _.+1 => m; elim: m n => /= [| m IH] n;
    case: ifP => // H; move/IH; rewrite (leq_eqVlt n) orbC => ->.
Qed.

Require Import regexp pumping.

Lemma nseq_eq_cat T (x : T) n xs ys :
  nseq n x = xs ++ ys -> nseq (size xs) x = xs /\ nseq (size ys) x = ys.
Proof.
  elim: n xs ys => //=.
  - by do 2 case => //.
  - move => n IH [] //=.
    + by case => //= y ys [] H H0; subst y ys; rewrite size_nseq.
    + by move => a xs ys [] H; subst a; case/IH => {2}<- {2}<-.
Qed.

Lemma size_rep (T : finType) (xs : seq T) n :
  size (rep xs n) = n * size xs.
Proof. by elim: n => //= n H; rewrite size_cat H mulSn. Qed.

Lemma prime_non_regular (T : finType) (c : T) :
  ~ regular (fun (s : seq T) => prime (size s)).
Proof.
  apply pumping => k.
  exists (nseq (next_prime k.+2 - k) c), (nseq k c), [::].
  split; last split; last move => u v w H H0.
  - by rewrite size_nseq.
  - rewrite cats0 size_cat !size_nseq subnK.
    + apply next_prime_is_prime.
    + apply leq_trans with k.+2.
      * by do 2 apply leqW.
      * apply next_prime_spec3.
  - case/(nseq_eq_cat T): (H) => H1; case/(nseq_eq_cat T) => H2 H3.
    move: H H0; rewrite -{}H1 -{}H2 -{}H3.
    move: {u v w} (size u) (size v) (size w) => u v w.
    rewrite !cat_nseq_eq addnA.
    move/(f_equal size); rewrite !size_nseq => -> {k} H.
    exists (next_prime (u + v + w).+2 - v).
    rewrite
      cats0 !size_cat size_rep !size_nseq (addnC (_ * _)) (addnA u) addnAC.
    move: {u w} (u + w) => u.
    rewrite addnA (addnC (_ - _)) addnBA.
    + rewrite (addnC u) subnDA addnK -mulnS.
      apply/negP/primePn; right; exists v.+1; last by rewrite dvdn_mull.
      rewrite ltnS; case: v H => //= v _; apply ltn_Pmull => //.
      rewrite ltn_subRL addn1 -!addnS; apply leq_trans with (u + v.+3).
      * by apply leq_addl.
      * by apply next_prime_spec3.
    + apply leq_trans with (u + v).+2.
      * by do 2 apply leqW.
      * apply next_prime_spec3.
Qed.
