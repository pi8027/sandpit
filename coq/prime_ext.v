(*
(add-to-list 'coq-load-path "~/src/coq/regular/")
*)

Require Import
  ssreflect ssrfun ssrbool eqtype ssrnat seq fintype div bigop prime binomial.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma primeP' p :
  reflect (1 < p /\ forall p', p' < p -> prime p' -> ~ p' %| p) (prime p).
Proof.
  case/boolP: (prime p) => H; constructor; [split | case].
  - by move: p H; do 2 case => //.
  - case/primeP: H => H H0 p' H1 H2; case/(H0 p')/orP.
    + by move: p' H2 {H1}; do 2 case => //.
    + by rewrite (ltn_eqF H1).
  - move => H0 H1; case/primePn: H; first by move: p H0 {H1}; do 2 case => //.
    case => x; case/andP => H2 H3 H4; apply (H1 (pdiv x)).
    + by apply leq_ltn_trans with x => //; apply pdiv_leq, ltnW.
    + by apply pdiv_prime.
    + by apply dvdn_trans with x => //; apply pdiv_dvd.
Qed.

Fixpoint search_prime n m :=
  if prime n
    then n
    else if m is m.+1
      then search_prime n.+1 m
      else 0.

Definition next_prime n := search_prime n n`!.+1.

Lemma next_prime_is_prime n : prime (next_prime n).
Proof.
  suff: next_prime n != 0 by
    rewrite /next_prime; move: n`!.+1 => m;
      elim: m n => /= [| m IH] n; case: ifP => //= _; apply IH.
  rewrite /next_prime; apply/negP => H.
  have {H} H p : n <= p <= n`!.+1 + n -> ~~ prime p.
    move: H; move: n`!.+1 => m; elim: m n => /= [| m IH] n.
    - by rewrite add0n -eqn_leq => H; move/eqP => <-;
        apply/negP => H0; move: H; rewrite H0 /=; case: n H0.
    - case: ifP; first by case: n.
      move => H; move/IH => {IH} H0; rewrite leq_eqVlt; case/andP; case/orP.
      + by move/eqP => <-; rewrite H.
      + by rewrite addSnnS => H1 H2; apply/H0/andP.
  suff: prime n`!.+1
    by apply/negP/H; rewrite leq_addr andbT {H}; apply leqW;
      case: n => //= n; rewrite factS -{1}(muln1 n.+1) leq_mul2l fact_gt0.
  apply/primeP'; split; first by rewrite ltnS fact_gt0.
  move => p'; rewrite ltnS => H0 H1 H2; case (leqP p' n) => H3;
    last by move: (H p'); rewrite (ltnW H3);
      move/(_ (leq_trans (leqW H0) (leq_addr _ _)))/negP.
  move: H2; rewrite -addn1 dvdn_addr;
    first by rewrite dvdn1; move/eqP => ?; subst p'; move: H1.
  by rewrite -(ffact_fact (leq_subr p' n)) subKn //; apply dvdn_mull;
    case: p' H1 {H H0 H3} => // p' _; rewrite factS; apply dvdn_mulr.
Qed.

Lemma next_prime_smallest n p : n <= p < next_prime n -> ~~ prime p.
Proof.
  move: (next_prime_is_prime n).
  rewrite /next_prime; move: n`!.+1 => m.
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

Hint Resolve next_prime_is_prime next_prime_smallest next_prime_spec3.

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

Lemma rev_nseq T n (x : T) : rev (nseq n x) = nseq n x.
Proof.
  by elim: n => //= n; rewrite rev_cons => ->; elim: n => //= n ->.
Qed.

Lemma prime_not_regular (T : finType) (c : T) :
  ~ regular (fun s : seq T => prime (size s)).
Proof.
  apply pumping => k; exists (nseq (next_prime k.+2 - k) c), (nseq k c), [::];
    do !split; last move => u v w H.
  - by rewrite size_nseq.
  - by rewrite cats0 size_cat !size_nseq subnK //;
      apply leq_trans with k.+2 => //; do 2 apply leqW.
  - case/(@nseq_eq_cat T): H (H) => <-; case/(@nseq_eq_cat T) => <- <-.
    move: {u v w} (size u) (size v) (size w) => u v w.
    rewrite !cat_nseq_eq addnA.
    move/(f_equal size); rewrite !size_nseq => -> {k}; case: v => // v _.
    exists (next_prime (u + v.+1 + w).+2 - v.+1).
    rewrite cats0 !size_cat size_rep !size_nseq (addnCA u) addnAC.
    move: {u w} (u + w) => u; rewrite addnC -addnA addnBA.
    + rewrite subnDA addKn addnC -mulnS.
      apply/negP/primePn; right; exists v.+2; last by rewrite dvdn_mull.
      by rewrite !ltnS /=; apply ltn_Pmull => //;
        rewrite ltn_subRL addn1 -!addnS;
        apply leq_trans with (u + v.+3) => //; apply leq_addl.
    + by apply leq_trans with (u + v.+1).+2 => //; do 2 apply leqW.
Qed.

Goal forall (T : finType) (a b : T),
  a != b ->
  ~ regular (fun s => count (fun c => c == a) s = count (fun c => c == b) s).
Proof.
  move => T a b; move/negbTE => H.
  apply pumping => k.
  exists [::], (nseq k a), (nseq k b).
  rewrite cat0s size_nseq leqnn !count_cat !non_regular.count_nseq
          !eqxx (@eq_sym _ b a) H /= mul1n mul0n addn0 add0n.
  do !split.
  move => u v w H0.
  case/(@nseq_eq_cat T): H0 (H0) => <-; case/(@nseq_eq_cat T) => <- <-.
  move: {u v w} (size u) (size v) (size w) => u v w.
  rewrite !cat_nseq_eq addnA.
  move/(f_equal size); rewrite !size_nseq => -> {k}; case: v => // v _.
  exists 0 => /=; move/eqP.
  by rewrite !count_cat !non_regular.count_nseq !eqxx (@eq_sym _ b a) H /=
          !mul1n !mul0n !add0n -addnA eqn_add2l addnC eqn_add2r.
Qed.

Lemma palindromes_not_regular (T : finType) (a b : T) :
  a != b -> ~ regular (fun s : seq T => s = rev s).
Proof.
  move/negbTE => H; apply pumping => k.
  exists [::], (nseq k a), (b :: nseq k a).
  rewrite size_nseq /= rev_cat rev_cons -cats1 -catA /= rev_nseq.
  do !split => //.
  move => u v w H0.
  case/(@nseq_eq_cat T): H0 (H0) => <-; case/(@nseq_eq_cat T) => <- <-.
  move: {u v w} (size u) (size v) (size w) => u v w.
  rewrite !cat_nseq_eq addnA.
  move/(f_equal size); rewrite !size_nseq => -> {k}; case: v => // v _.
  exists 0 => /=; move/eqP.
  by rewrite
    !rev_cat rev_cons -cats1 -!catA /= !rev_nseq catA !cat_nseq_eq
    addnAC -(cat_nseq_eq (u + w)) -catA eqseq_cat // eqxx eqE /= eq_sym H /=.
Qed.
