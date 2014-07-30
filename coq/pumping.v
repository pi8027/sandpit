(*
(add-to-list 'coq-load-path "~/src/coq/regular/")
*)

Require Import
  ssreflect ssrfun ssrbool eqtype ssrnat seq fintype div bigop prime binomial
  dfa_to_re regexp pumping.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Set Printing Width 77.

(* 1 *)

Check regular.
Check pumping.

Lemma nseq_eq_cat T (x : T) n xs ys :
  nseq n x = xs ++ ys -> nseq (size xs) x = xs /\ nseq (size ys) x = ys.
Proof.
  elim: n xs ys => //=.
  - by do 2 case => //.
  - move => n IH [] //=.
    + by case => //= y ys [] H H0; subst y ys; rewrite size_nseq.
    + by move => a xs ys [] H; subst a; case/IH => {2}<- {2}<-.
Qed.

Lemma anbn_non_regular (T : finType) (a b : T) :
  a != b -> ~ regular (fun s => exists n, s = nseq n a ++ nseq n b).
Proof.
  move/negbTE => H; apply pumping => k.
  exists [::], (nseq k a), (nseq k b).
  rewrite size_nseq leqnn /=; do ! split; first by exists k.
  move => u v w H0.
  move: H0 (H0); do 2 case/(@nseq_eq_cat T) => <-; move => <-.
  move: {u v w} (size u) (size v) (size w) => u v w.
  rewrite !cat_nseq_eq addnA.
  move/(f_equal size); rewrite !size_nseq => -> {k}; case: v => // v _.
  exists 0; case => /= x H0.
  move: (f_equal (count (fun c => c == b)) H0)
        (f_equal (count (fun c => c == a)) H0).
  by rewrite !count_cat !non_regular.count_nseq !eqxx eq_sym H !mul1n !mul0n;
    nat_norm => <- /eqP; rewrite addnCA -addSn -{1}(add0n (u + w)) eqn_add2r.
Qed.

(* 2 *)

Goal forall (T : finType) (a b : T),
  a != b ->
  ~ regular (fun s => count (fun c => c == a) s = count (fun c => c == b) s).
Proof.
  move => T a b /negbTE H; apply pumping => k.
  exists [::], (nseq k a), (nseq k b).
  rewrite size_nseq leqnn !count_cat !non_regular.count_nseq
          !eqxx (eq_sym b a) !H /= mul1n mul0n addn0 add0n.
  do !split; move => u v w H0.
  move: H0 (H0); do 2 case/(@nseq_eq_cat T) => <-; move => <-.
  move: {u v w} (size u) (size v) (size w) => u v w.
  rewrite !cat_nseq_eq addnA.
  move/(f_equal size); rewrite !size_nseq => -> {k}; case: v => // v _.
  exists 0 => /=; move/eqP.
  by rewrite !count_cat !non_regular.count_nseq !eqxx (eq_sym b a) H
             !mul1n !mul0n -addnA eqn_add2l addnC eqn_add2r.
Qed.

Lemma starAtomP (T : eqType) (c : T) (w : word T) :
  reflect (w = nseq (size w) c) (w \in star (atom c)).
Proof.
  apply (iffP idP).
  - case/starP => ws H -> {w}; elim: ws H => //= w ws H /andP [/andP [_]].
    by rewrite inE => /eqP -> /H {1}->.
  - by move => ->; move: {w} (size w) => n; apply/starP;
      exists (nseq n [:: c]); elim: n => //= n ->; first rewrite inE eqxx.
Qed.

Goal forall (T : finType) (a b : T),
  a != b ->
  ~ regular (fun s => count (fun c => c == a) s = count (fun c => c == b) s).
Proof.
  move => T a b H H0; apply (anbn_non_regular H).
  move/negbTE: H H0 => H.
  rewrite /regular; move => [x Hx].
  exists (Inter x (Conc (Star (Atom a)) (Star (Atom b)))) => w.
  rewrite Inter_correct; split;
    [ case => n ->; apply/andP; split; first apply Hx |
      case/andP => [] /Hx H0 ].
  - by rewrite !count_cat !non_regular.count_nseq
               !eqxx (eq_sym b a) H mul0n addn0.
  - apply/concP; exists (nseq n a), (nseq n b); split => //.
    by split; apply/starAtomP; rewrite size_nseq.
  - move => /concP [w1] [w2] [H1] [] /starAtomP H2 /starAtomP H3.
    subst w; move: H2 H3 H0 => -> ->; move: {w1 w2} (size w1) (size w2) => m n.
    by rewrite !count_cat !non_regular.count_nseq
               !eqxx (eq_sym b a) H !mul1n !mul0n add0n addn0 => ->; exists n.
Qed.

(* 3 *)

Lemma rev_nseq T n (x : T) : rev (nseq n x) = nseq n x.
Proof. by elim: n => //= n; rewrite rev_cons => ->; elim: n => //= n ->. Qed.

Lemma palindromes_non_regualr (T : finType) (a b : T) :
  a != b -> ~ regular (fun s : seq T => s = rev s).
Proof.
  move/negbTE => H; apply pumping => k.
  exists [::], (nseq k a), (b :: nseq k a).
  rewrite size_nseq /= rev_cat rev_cons -cats1 -catA /= rev_nseq.
  do !split => //; move => u v w H0.
  case/(@nseq_eq_cat T): H0 (H0) => <-; case/(@nseq_eq_cat T) => <- <-.
  move: {u v w} (size u) (size v) (size w) => u v w.
  rewrite !cat_nseq_eq addnA.
  move/(f_equal size); rewrite !size_nseq => -> {k}; case: v => // v _.
  exists 0 => /=; move/eqP.
  rewrite !rev_cat rev_cons !rev_nseq -cats1 -!catA catA !cat_nseq_eq addnAC.
  by rewrite -{2}(cat_nseq_eq (u + w)) -catA eqseq_cat //= eqxx eqE /= eq_sym H.
Qed.

(* 4 *)

Lemma dvdn_fact m n : 0 < m <= n -> m %| n`!.
Proof.
  case: m => //= m; elim: n => //= n IHn; rewrite ltnS leq_eqVlt.
  by case/predU1P=> [-> | /IHn]; [apply: dvdn_mulr | apply: dvdn_mull].
Qed.

Lemma rep_nseq (T : eqType) (a : T) m n : rep (nseq n a) m = nseq (m * n) a.
Proof. by elim: m => //= m ->; rewrite cat_nseq_eq mulSn. Qed.

Lemma complement_of_palindromes_non_regular (T : finType) (a b : T) :
  a != b -> ~ regular (fun s : seq T => s != rev s).
Proof.
  move/negbTE => H; apply pumping => k.
  exists [::], (nseq k a), (b :: nseq (k + k`!) a).
  rewrite
    size_nseq /= rev_cat rev_cons -cats1 rev_nseq -{2}cat_nseq_eq -!catA
    eqseq_cat // eqxx /= -{2}(ltn_predK (fact_gt0 k)) {1}/eq_op /= eq_sym H /=.
  do !split => //; move => u v w H0.
  case/(@nseq_eq_cat T): H0 (H0) => <-; case/(@nseq_eq_cat T) => <- <-.
  move: {u v w} (size u) (size v) (size w) => u v w.
  rewrite !cat_nseq_eq addnA.
  move/(f_equal size); rewrite !size_nseq => -> {k}; case: v => // v _.
  have/dvdn_fact/dvdnP[n ->] : 0 < v.+1 <= u + v.+1 + w
    by rewrite addnAC addnS !ltnS leq0n leq_addl.
  exists n.+1; apply/negP/negPn/eqP.
  rewrite rep_nseq !rev_cat rev_cons -cats1 !rev_nseq.
  rewrite !(catA, cat_nseq_eq) -!catA !cat_nseq_eq /=.
  repeat match goal with |- @eq nat _ _ => idtac | |- _ => f_equal end.
  - by rewrite (addnAC u v.+1) -(addnA _ v.+1) -mulSn addnAC.
  - by rewrite (addnAC u) -addnA -mulSn (addnC u) addnAC addnA.
Qed.

(* 5 *)

Lemma prime_above m : {p | m < p & prime p}.
Proof.
  have /pdivP[p pr_p p_dv_m1]: 1 < m`! + 1 by rewrite addn1 ltnS fact_gt0.
  exists p => //; rewrite ltnNge; apply: contraL p_dv_m1 => p_le_m.
  by rewrite dvdn_addr ?dvdn_fact ?prime_gt0 // gtnNdvd ?prime_gt1.
Qed.

Lemma size_rep (T : eqType) (xs : seq T) n : size (rep xs n) = n * size xs.
Proof. by elim: n => //= n H; rewrite size_cat H mulSn. Qed.

Lemma pumping_size (T : finType) (a : T) (L : nat -> Prop) :
  (forall k, exists x y : nat,
    k <= y /\ L (x + y) /\
    forall u v, y = u + v -> v != 0 -> exists i, L (x + u + i * v) -> False) ->
  ~ regular (fun s : seq T => L (size s)).
Proof.
  move => H; apply pumping => k; move: H => /(_ k) [x [y [H0 [H1 H]]]].
  exists (nseq x a), (nseq y a), [::]; rewrite !size_cat /= addn0 !size_nseq;
    do !split => //; move => {k H0 H1} u v w H0.
  case/(@nseq_eq_cat T): H0 (H0) H => <-; case/(@nseq_eq_cat T) => <- <-.
  move: {u v w} (size u) (size v) (size w) => u v w.
  move/(f_equal size); rewrite !size_cat !size_nseq => -> /(_ (u + w) v);
    case: v => // v; rewrite -addnA (addnC v.+1) => /(_ erefl erefl) [i H] _.
  by exists i; rewrite !size_cat size_rep !size_nseq /= addn0
                       (addnC (_ * _)) !addnA -(addnA x).
Qed.

Arguments pumping_size [T] _ _ _ _.

Lemma primes_non_regular (T : finType) (a : T) :
  ~ regular (fun s : seq T => prime (size s)).
Proof.
  apply (pumping_size a prime) => k {T a}.
  case: (prime_above k.+1) => p; move/subnK => <-; move: (p - k.+2) => {p} p Hp.
  exists p.+2, k; rewrite !addSnnS; do !split => //; move => u [] // v {Hp} _ _.
  exists (p.+2 + u); rewrite -mulnS; apply/negP/primePn; right; exists v.+2.
  - by rewrite ltnS /=; apply ltn_Pmull.
  - by rewrite dvdn_mull.
Qed.
