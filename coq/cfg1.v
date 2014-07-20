Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop fingroup ssralg
               ssrnum ssrint.
Import GRing.Theory Num.Theory.

Definition bval (b : bool) : int := (if b then 2 else - 1)%R.
Definition height (s : seq bool) : int := (\sum_(b <- s) bval b)%R.
Definition Lb (x : int) (s : seq bool) : bool := (x + height s == 0)%R.

Inductive Lp : seq bool -> Prop :=
  | Lp_empty : Lp [::]
  | Lp_app : forall s1 s2, Lp s1 -> Lp s2 -> Lp (s1 ++ s2)
  | Lp_rule1 : forall s, Lp s -> Lp (true :: s ++ [:: false; false])
  | Lp_rule2 : forall s, Lp s -> Lp (false :: false :: s ++ [:: true])
  | Lp_rule3 : forall s1 s2, Lp s1 -> Lp s2 ->
               Lp (false :: s1 ++ true :: s2 ++ [:: false]).

Lemma take_minn A n m (xs : seq A) : take n (take m xs) = take (minn n m) xs.
Proof. by elim: n m xs => [| n IH] [| m] [] // x xs; rewrite minnSS /= IH. Qed.

Theorem well_founded_lt : well_founded (fun n m => n < m).
Proof.
  move => x.
  move: {2}x (leqnn x) => n.
  elim: n x => [| n IHn] x H; constructor => y H0.
  - apply False_ind, notF; rewrite -(ltn0 y); apply (leq_trans H0 H).
  - apply IHn; rewrite -ltnS; apply (leq_trans H0 H).
Defined.

Fixpoint splitL (x : int) (s : seq bool) : seq bool * seq bool :=
  match s with
    | [::] => ([::], [::])
    | b :: s' =>
      let x' := (x + bval b)%R in
      if x' == 0%R
        then ([:: b], s')
        else let s'' := splitL x' s' in (b :: s''.1, s''.2)
  end.

Definition splitted (x : int) (s : seq bool) :=
  forall n, n < size s -> ~~ Lb x (take n s).

Lemma height0 : height [::] = 0%R.
Proof. by rewrite /height big_nil. Qed.

Lemma heightc b s : height (b :: s) = (bval b + height s)%R.
Proof. by rewrite /height big_cons. Qed.

Lemma heightcat s1 s2 : height (s1 ++ s2) = (height s1 + height s2)%R.
Proof. by rewrite /height big_cat. Qed.

Lemma Lb0 x : Lb x [::] = (0%R == x).
Proof. by rewrite /Lb height0 addr0. Qed.

Lemma Lbc x b s : Lb x (b :: s) = Lb (x + bval b) s.
Proof. by rewrite /Lb heightc addrA. Qed.

Lemma LbcatC x s1 s2 : Lb x (s1 ++ s2) = Lb x (s2 ++ s1).
Proof.  by rewrite /Lb !heightcat /= (addrC (height _)). Qed.

Lemma splitL_cat x s : s = (let s' := splitL x s in s'.1 ++ s'.2).
Proof. by elim: s x => //= b s H x; case: ifP => //= _; rewrite -H. Qed.

Lemma splitL_split x s : Lb x s ->
  let s' := splitL x s in Lb x s'.1 && Lb 0%R s'.2.
Proof.
  elim: s x => //=.
  - by move => x -> /=; rewrite Lb0.
  - move => b s IH x; case: ifP => /=.
    + by move/eqP => H; rewrite !Lbc Lb0 H => ->.
    + by rewrite !Lbc => _ H; apply IH.
Qed.

Lemma splitL_splitted (x : int) s : x != 0%R -> splitted x (splitL x s).1.
Proof.
  elim: s x => //= b s IH x H; case: ifP => /= H0.
  - by case => //; rewrite take0 Lb0 eq_sym.
  - case => /=.
    + by rewrite Lb0 eq_sym.
    + move => n; rewrite ltnS Lbc => H1.
      by apply (IH (x + bval b)%R) => //; rewrite H0.
Qed.

Lemma splitted_pn (x : int) s b :
  (0 < x)%R -> splitted x (rcons s b) ->
  forall n, n <= size s -> (0 < x + height (take n s))%R.
Proof.
  elim: s x => /=; first by move => x; rewrite height0 addr0.
  move => b' s IH x H H0 [_ | n] /=.
  - by rewrite height0 addr0.
  - rewrite ltnS heightc addrA; apply IH.
    + case: b' H0 => /=.
      * move => _; apply ltr_le_trans with x => //; apply ler_addl.
      * by move/(_ 1); rewrite /= size_rcons take0 Lbc Lb0 /=;
          move/(_ erefl) => H0; rewrite ltr_def eq_sym H0 /= subr_ge0 -gtz0_ge1.
    + by move => {n} n; move: (H0 n.+1) => /=; rewrite ltnS Lbc.
Qed.

Lemma splitted_last (x : int) s b :
  (0 < x)%R -> splitted x (rcons s b) -> (x + height (rcons s b) <= 2)%R ->
  b = false.
Proof.
  move => H H0 H1; move: {H H0} H1 (splitted_pn x s b H H0 (size s) (leqnn _)).
  rewrite take_size -cats1 heightcat heightc height0 addr0 addrA.
  case: b => //=; rewrite -{2}(add0r (2 : int)) ler_add2r => H H0.
  by move: (ltr_le_trans H0 H).
Qed.

Lemma splitted_catl x s1 s2 : splitted x (s1 ++ s2) -> splitted x s1.
Proof.
  by move => H n H0; move: (H n); rewrite size_cat;
    move/(_ (ltn_addr _ H0)); rewrite take_cat H0.
Qed.

Theorem LpLbP s : reflect (Lp s) (Lb 0%R s).
Proof.
  apply: (iffP idP).
  - move: {1}(size _) (erefl (size s)) => n; move: n s.
    refine (well_founded_ind well_founded_lt _ _);
      case => [| n] IH [] //; first constructor; move => b s H.
    move/splitL_split; move: H.
    rewrite {1 3}(splitL_cat 0 (b :: s)) /= size_cat;
      case: ifP => /=; first by case b.
    rewrite add0r addSn => _ [] H /andP [H0 H1]; apply (Lp_app (_ :: _));
      last by apply (IH (size (splitL (bval b) s).2)) => //;
              rewrite H ltnS leq_addl.
    have {n IH H H1} IH s' :
      size s' <= size (splitL (bval b) s).1 -> Lb 0 s' -> Lp s'
      by move => H2; apply (IH (size s')) => //;
        rewrite H -addSn; apply ltn_addr; rewrite ltnS.
    have/(splitL_splitted (bval b) s) : (bval b != 0) by case b.
    move: IH H0; rewrite Lbc add0r; case/lastP: {s} (fst _);
      first by rewrite Lb0; case: b.
    move: b => b' s b; (case: b'; last case: b) => /=.
    + rewrite size_rcons => IH H H0.
      move: (splitted_last 2 s b erefl H0); move: (H);
        rewrite /Lb => /eqP -> /(_ erefl) H1; subst b.
      move: H H0; rewrite -cats1 LbcatC Lbc /= => H /splitted_catl.
      case/lastP: s IH H; first by move => _; rewrite Lb0 //.
      move => s b; rewrite size_rcons => IH H H0.
      move: (splitted_last 2 s b erefl H0); move: (H);
        rewrite /Lb eq_sym addrC -subr_eq eq_sym =>
        /eqP -> /(_ erefl) H1; subst b;
      move: H H0; rewrite -cats1 LbcatC Lbc -catA /= => H H0.
      constructor; apply IH => //; apply (leq_addl 2).
    + case: s => /=; first by rewrite Lbc Lb0.
      case; last by move => l IH; rewrite Lbc -cats1 LbcatC Lbc /= => H _;
        constructor; apply IH => //; rewrite size_rcons; apply (leq_addl 2).
      move => s _;
        rewrite Lbc /Lb /= eq_sym addrC -subr_eq eq_sym sub0r => /eqP H H0.
      have {H0} H0: splitted 1 (rcons s true)
        by move => n H1; move: (H0 n.+1) => /=; rewrite ltnS Lbc /=; move/(_ H1).
      by move: (splitted_last 1 s true erefl H0); rewrite H; move/(_ erefl).
    + rewrite -cats1 LbcatC Lbc /= => H H0 /splitted_catl.
      case/(splitL_split (- (2 : int)))/andP: H0 => /=; move: H.
      rewrite {1 4 5}(splitL_cat (- (2 : int)) s) !size_cat /= addn1.
      move: (splitL_splitted (- (2 : int))%R s erefl).
      case/lastP: {s} (fst _) (snd _) => /=; first by rewrite Lb0.
      move => s1 [] s2.
      * rewrite -cats1 LbcatC Lbc /= -!catA => _ IH H H0 _; constructor;
          apply IH => //; rewrite size_cat /= addn1.
        - rewrite addSnnS -addnS; apply leq_addr.
        - rewrite -addSn; apply leq_addl.
      * rewrite -cats1 -catA; move => /splitted_catl H _ H0 _ /splitted_catl H1;
          apply False_ind; move: {s2} H0 H H1; rewrite LbcatC Lbc /=.
        have: (- (2 : int) - 1 < - (2 : int))%R by [].
        elim/last_ind: s1 (- _ - _)%R;
          first by move => x H; rewrite Lb0 => /eqP H1; rewrite -H1 in H.
        move => /= s b IH x H; rewrite -cats1 LbcatC Lbc /= => H0 H1 H2.
        move: (splitted_catl _ _ _ H1) (splitted_catl _ _ _ H2);
          apply (IH (x + bval b)%R) => //.
        move: {H1 H2} (H1 (size s)) (H2 (size s));
          rewrite size_cat /= addn1 leqnn take_cat ltnn subnn take0 cats0 =>
          /(_ erefl) H1 /(_ erefl) H2.
        case: b H0 => //=;
          last by move => _; apply ler_lt_trans with x => //;
                  rewrite -{2}(subr0 x); apply ler_add.
        move => H3; move: H3 H1 H2; rewrite /Lb !addr_eq0 => /eqP <-.
        by rewrite ltr_def => -> /=; rewrite -ltz_add1r ltr_def => -> /=;
          rewrite -ler_subr_addr -ltz_add1r.
  - rewrite /Lb add0r; move: s.
    refine (Lp_ind _ _ _ _ _ _) => //= [| s1 s2 | s | s | s1 s2];
      rewrite !(height0, heightc, heightcat); do 3 move => // _ /eqP ->.
Qed.
