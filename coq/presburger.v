(*
(add-to-list 'coq-load-path "~/src/coq/regular/")
*)

Require Import
  ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple finfun div
  bigop ssralg ssrnum ssrint intdiv
  dfa_to_re regexp automata.
Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Theorem well_founded_ltof (A : Type) (f : A -> nat) :
  well_founded (fun n m => f n < f m).
Proof.
  move => x.
  move: {2}(f x) (leqnn (f x)) => n.
  elim: n x => [ | n IHn ] x H; constructor => y H0.
  - apply False_ind, notF.
    rewrite -(ltn0 (f y)).
    apply (leq_trans H0 H).
  - apply IHn.
    rewrite -ltnS.
    apply (leq_trans H0 H).
Defined.

(* extensions for fintype *)

Section Range.

Variables (i k : int).

Inductive range : predArgType := Range j of ((i <= j) && (j <= k))%R.

Coercion int_of_range r := let: (Range j _) := r in j.

Canonical range_subType := [subType for int_of_range].
Definition range_eqMixin := Eval hnf in [eqMixin of range by <:].
Canonical range_eqType := Eval hnf in EqType range range_eqMixin.
Definition range_choiceMixin := [choiceMixin of range by <:].
Canonical range_choiceType := Eval hnf in ChoiceType range range_choiceMixin.
Definition range_countMixin := [countMixin of range by <:].
Canonical range_countType := Eval hnf in CountType range range_countMixin.
Canonical range_subCountType := [subCountType of range].

Lemma lb_range (r : range) : (i <= r)%R.
Proof. by case: r => /= j /andP []. Qed.

Lemma ub_range (r : range) : (r <= k)%R.
Proof. by case: r => /= j /andP []. Qed.

Lemma range_inj : injective int_of_range.
Proof. exact: val_inj. Qed.

Definition range_enum : seq range :=
  pmap insub
    (map Negz (match i with Negz i' => iota 0 i'.+1 | _ => [::] end) ++
     map Posz (match k with Posz k' => iota 0 k'.+1 | _ => [::] end)).

Lemma range_enum_uniq : uniq range_enum.
Proof.
  rewrite pmap_sub_uniq // cat_uniq !map_inj_in_uniq;
    first (case: i => i'; case: k => k'; rewrite ?iota_uniq // andTb andbT).
  - by rewrite -all_predC /=; elim: map.
  - rewrite -all_predC all_map.
    elim: (iota 0 k'.+1) => //= n ns ->; rewrite andbT.
    by rewrite !inE /=; elim: iota.
  - by move => /= x y _ _ [].
  - by move => /= x y _ _ [].
Qed.

Lemma mem_range_enum r : r \in range_enum.
Proof.
  rewrite -(mem_map range_inj) /= /range_enum.
  case: r => /= j /andP [H H0]; rewrite pmap_filter;
    last by move => j'; case: insubP.
  rewrite mem_filter mem_cat; apply/andP; split;
    first by case: insubP => //; rewrite H H0.
  apply/orP; case: j H H0 => j' H H0; [right | left];
    (rewrite mem_map; last by move => ? ? []).
  - by case: k H0 => // k' H0; rewrite (mem_iota 0 k'.+1).
  - by case: i H => // i' H; rewrite (mem_iota 0 i'.+1) leq0n ltnS.
Qed.

Definition range_finMixin :=
  Eval hnf in UniqFinMixin range_enum_uniq mem_range_enum.
Canonical range_finType := Eval hnf in FinType range range_finMixin.
Canonical range_subFinType := Eval hnf in [subFinType of range].

End Range.

(* term and formula of Presburger arithmetic *)

Inductive term (v : nat) :=
  | t_const   of nat
  | t_var     of 'I_v
  | t_add     of term v & term v
  | t_mulc    of nat & term v.

Inductive formula (v : nat) :=
  | f_all     of formula v.+1
  | f_exists  of formula v.+1
  | f_neg     of formula v
  | f_and     of formula v & formula v
  | f_or      of formula v & formula v
  | f_leq     of term v & term v.

(* normal form of Prethburger formula *)

Inductive nformula (v : nat) :=
  | nf_exists of nformula v.+1
  | nf_neg    of nformula v
  | nf_or     of nformula v & nformula v
  | nf_atomic of int ^ v & int.

(* semantics of Presburger arithmetic  *)

Definition cons_tuple (A : Type) n (h : A) (t : A ^ n) : A ^ n.+1 :=
  [ffun m =>
   match m with
     | Ordinal 0 Hm => h
     | Ordinal m.+1 Hm =>
       t (@Ordinal n m (eq_ind (m.+1 < n.+1) is_true Hm (m < n) (ltnS _ _)))
   end].

Fixpoint term_val fvs (t : term fvs) (assign : nat ^ fvs) : nat :=
  match t with
    | t_const n => n
    | t_var v => assign v
    | t_add t t' => term_val t assign + term_val t' assign
    | t_mulc n t => n * term_val t assign
  end.

Fixpoint formula_semantics fvs (f : formula fvs) : nat ^ fvs -> Prop :=
  match f with
    | f_all f =>
      fun assign => forall n : nat, formula_semantics f (cons_tuple n assign)
    | f_exists f =>
      fun assign => exists n : nat, formula_semantics f (cons_tuple n assign)
    | f_neg f => fun assign => ~ formula_semantics f assign
    | f_and f f' =>
      fun assign => formula_semantics f assign /\ formula_semantics f' assign
    | f_or f f' =>
      fun assign => formula_semantics f assign \/ formula_semantics f' assign
    | f_leq t t' => fun assign =>  term_val t assign <= term_val t' assign
  end.

Fixpoint nformula_semantics fvs (f : nformula fvs) : nat ^ fvs -> Prop :=
  match f with
    | nf_exists f =>
      fun assign => exists n : nat, nformula_semantics f (cons_tuple n assign)
    | nf_neg f => fun assign => ~ nformula_semantics f assign
    | nf_or f f' =>
      fun assign => nformula_semantics f assign \/ nformula_semantics f' assign
    | nf_atomic t n => fun assign => (\sum_(m < fvs) t m * assign m <= n)%R
  end.

(* normal form computation *)

Fixpoint normal_t fvs (t : term fvs) : int ^ fvs * int :=
  (* a_1 x_1 + ... + a_n x_n + m *)
  match t with
    | t_const n => ([ffun => 0%R], (n : int))
    | t_var v => ([ffun v' => (v == v' : int)], 0%R)
    | t_add t t' =>
      let: (cs, n) := normal_t t in
      let: (cs', m) := normal_t t' in
      ([ffun var => cs var + cs' var], n + m)%R
    | t_mulc c t =>
      let: (cs, n) := normal_t t in
      ([ffun var => (c : int) * cs var], (c : int) * n)%R
  end.

Fixpoint normal_f fvs (f : formula fvs) : nformula fvs :=
  match f with
    | f_all f => nf_neg (nf_exists (nf_neg (normal_f f)))
    | f_exists f => nf_exists (normal_f f)
    | f_neg f => nf_neg (normal_f f)
    | f_and f f' => nf_neg (nf_or (nf_neg (normal_f f)) (nf_neg (normal_f f')))
    | f_or f f' => nf_or (normal_f f) (normal_f f')
    | f_leq t t' =>
      let: (cs, n) := normal_t t in
      let: (cs', m) := normal_t t' in
      nf_atomic [ffun var => cs var - cs' var]%R (m - n)%R
  end.

(* correctness proof *)

Lemma nt_correctness fvs (t : term fvs) assign :
  (term_val t assign : int) =
  (let (c, n) := normal_t t in \sum_(m < fvs) c m * assign m + n)%R.
Proof.
  elim: t assign => /=.
  - move => n assign; rewrite -{1}(add0r (n : int)); f_equal.
    apply big_ind => //.
    + by move => x y <- <-.
    + by move => ? _; rewrite ffunE mul0r.
  - move => v assign; rewrite addr0.
    rewrite (bigID (eq_op^~ v)) /= -{1}(addr0 (assign v : int)); f_equal.
    + by rewrite big_pred1_eq ffunE eqxx mul1r.
    + apply big_ind => //.
      * by move => x y <- <-.
      * by move => ? /negPf; rewrite ffunE eq_sym => -> /=; rewrite mul0r.
  - move => t; case_eq (normal_t t) => cs n _ IHt.
    move => t'; case_eq (normal_t t') => cs' m _ IHt' i.
    rewrite PoszD IHt IHt' !addrA (addrAC _ n); do 2 f_equal.
    by rewrite -big_split /=; apply eq_big => // var _; rewrite ffunE mulrDl.
  - move => c t; case_eq (normal_t t) => cs n H IH i.
    rewrite PoszM IH mulrDr big_distrr /=.
    by f_equal; apply eq_big => // var _; rewrite ffunE mulrA.
Qed.

Lemma nf_correctness fvs (f : formula fvs) assign :
  (forall fvs (f : nformula fvs) assign,
    let P := nformula_semantics f assign in ~ ~ P -> P) ->
  (formula_semantics f assign <-> nformula_semantics (normal_f f) assign).
Proof.
  move => dne; move: fvs f assign; refine (formula_ind _ _ _ _ _ _) => /=.
  - move => fvs f IH assign; split => H.
    + by case => a; apply; apply IH, H.
    + by move => a; apply IH, dne => H0; apply H; exists a.
  - by move => fvs f IH assign; split; case => a H; exists a; apply IH.
  - by move => fvs f IH assign; split => H H0; apply H, IH.
  - move => fvs f IHf f' IHf' assign; split.
    + by case => H H0 []; apply; [apply IHf | apply IHf'].
    + by move => H; split; [apply IHf | apply IHf'];
        apply dne => H'; apply H; [left | right].
  - by move => fvs f IHf f' IHf' assign; split;
      (case => H; [left; apply IHf | right; apply IHf']).
  - move => fvs t t' assign; rewrite -lez_nat !nt_correctness.
    case_eq (normal_t t); case_eq (normal_t t') => /= cs n _ cs' m _.
    rewrite -ler_subr_addr -addrA addrC -ler_subl_addr
      (@big_morph _ _ -%R%R 0%R _ 0%R _ (@opprD _)) ?oppr0 // -big_split /=.
    set x := BigOp.bigop _ _ _; set y := BigOp.bigop _ _ _.
    suff ->: x = y by []; rewrite {}/x {}/y.
    by apply eq_big => // var _; rewrite ffunE mulrDl mulNr.
Qed.

(* automata construction *)

Lemma lez_divL d m n : (0 < d -> m <= n * d -> m %/ d <= n)%Z%R.
Proof.
  move => H H0; rewrite -(ler_pmul2r H); apply: (ler_trans _ H0).
  rewrite -[X in (X <= _)%R]addr0 {2}(divz_eq m d) ler_add2l.
  by apply modz_ge0, lt0r_neq0.
Qed.

Definition dfa_all A : dfa A :=
  {| dfa_s := tt; dfa_fin x := true; dfa_trans x a := tt |}.

Lemma dfa_all_correct A q w : dfa_accept (dfa_all A) q w.
Proof. by elim: w q => /=. Qed.

Section automata_construction.

Variables (fvs : nat) (cs : int ^ fvs).

Lemma word_of_assign_decreasing (a : nat ^ fvs) :
  a != [ffun=> 0] ->
  \sum_(i < fvs) [ffun i0 => a i0 %/ 2] i < \sum_(i < fvs) a i.
Proof.
  move => H; rewrite ltnNge; apply/negP => H0; move/eqP: H;
    apply; apply/ffunP => /= i; rewrite ffunE; apply/eqP.
  have/(leq_trans H0) {H0} :
    \sum_(i < fvs) [ffun i' => a i' %/ 2] i <= (\sum_(i < fvs) a i) %/ 2 by
    apply (big_rec2 (fun x y => is_true (x <= y %/ 2))) =>
      //= {i} i x y _; rewrite ffunE !leq_divRL // mulnDl;
      apply leq_add, leq_trunc_div.
  rewrite leq_divRL // => H.
  have {H}: \sum_(i < fvs) a i == 0 by
    case: (BigOp.bigop _ _ _) H => // n; rewrite leqNgt mulSn !ltnS leq_pmulr.
  by apply contraTT => H; rewrite (bigID (eq_op^~ i)) /= big_pred1_eq;
    case: (a i) H.
Qed.

Definition word_of_assign : nat ^ fvs -> seq (bool ^ fvs) :=
  Fix
    (well_founded_ltof (fun (a : nat ^ fvs) => \sum_(i < fvs) a i))
    (fun _ => seq (bool ^ fvs))
    (fun a IH =>
      (if a == [ffun => 0] as x return (a == [ffun => 0]) = x -> _
       then fun _ => [::]
       else fun H => [ffun i => odd (a i)] ::
                     IH _ (word_of_assign_decreasing (negbT H)))
      (erefl (a == [ffun => 0]))).

Fixpoint assign_of_word (w : seq (bool ^ fvs)) : nat ^ fvs :=
  match w with
    | [::] => [ffun => 0]
    | ch :: w => [ffun i => ch i + assign_of_word w i * 2]
  end.

Lemma cancel_woa_aow : cancel word_of_assign assign_of_word.
Proof.
  rewrite /cancel.
  apply (well_founded_induction
    (well_founded_ltof (fun (a : nat ^ fvs) => \sum_(i < fvs) a i))) =>
    assign IH.
  rewrite /word_of_assign /Fix -Fix_F_eq.
Admitted.

Section dfa_of_atomic_formula_definition.

Variable (n : int).

Definition state_lb : int := Num.min n (- \sum_(i : 'I_fvs | 0 <= cs i) cs i)%R.
Definition state_ub : int := Num.max n (- \sum_(i : 'I_fvs | cs i <= 0) cs i)%R.

Lemma afdfa_s_proof : (state_lb <= n <= state_ub)%R.
Proof. by rewrite /state_lb /state_ub ler_minl ler_maxr lerr. Qed.

Lemma afdfa_trans_proof (q : range state_lb state_ub) (ch : bool ^ fvs) :
  (state_lb <=
   ((int_of_range q - \sum_(i : 'I_fvs | ch i) cs i) %/ 2)%Z <=
   state_ub)%R.
Proof.
  case: q => /= q /andP [].
  rewrite /state_lb /state_ub !lez_divRL // => H H0.
  by apply/andP; split;
    [case: minrP H {H0} => H H0 |
     case: maxrP H0 {H} => H H0; apply lez_divL => //];
  rewrite mulz2 ler_add //; [apply (ler_trans H) | | apply: (ler_trans _ H) |];
  rewrite ler_opp2 big_mkcond [X in (_ <= X)%R]big_mkcond /=;
  apply (big_ind2 (fun (x y : int) => (x <= y)%R) (lerr 0) (@ler_add _)) => i _;
  do 2 case: ifP => //; [| | move => _ | move => _] => /negbT;
    rewrite -ltrNge ltr_def => /andP [].
Qed.

Definition dfa_of_af : dfa [finType of bool ^ fvs] :=
  {| dfa_state := [finType of range state_lb state_ub];
     dfa_s := Range afdfa_s_proof;
     dfa_fin q := (0 <= q)%R;
     dfa_trans q ch := Range (afdfa_trans_proof q ch)
  |}.

End dfa_of_atomic_formula_definition.

Lemma af_validP (n : int) :
  reflect
    (forall assign, nformula_semantics (nf_atomic cs n) assign)
    (dfa_equiv (dfa_of_af n) (dfa_all _)).
Proof.
  suff: forall assign,
    assign \in dfa_lang (dfa_of_af n) <->
    (\sum_(m < fvs) cs m * (assign_of_word assign) m <= n)%R.
    move => H; apply: (iffP idP) => /=;
      [move/dfa_equiv_correct => H0 assign |
       move => H0; apply/dfa_equiv_correct => assign].
    - by rewrite -(cancel_woa_aow assign); apply H;
        rewrite H0 delta_accept unfold_in.
    - by apply esym; rewrite delta_accept unfold_in; apply esym, H, H0.
  move => assign; rewrite delta_accept unfold_in /=.
  elim: assign {2 3 10 11}n (afdfa_s_proof n) =>
    /= [| ch assign IH] n' H.
  - have -> //: (\sum_(m < fvs) cs m * [ffun => 0%N] m = 0)%R.
    by apply big_rec => //= i x _ ->; rewrite ffunE mulr0.
  - rewrite delta_cons /=.
    apply (iff_trans (IH _ _)).
    rewrite lez_divRL // ler_subr_addr.
    set x := (_ + _)%R; set y := BigOp.bigop _ _ _.
    have -> // : x = y; rewrite {}/x {}/y.
    rewrite (big_morph (fun x => (x * (2 : int))%R) (id1 := 0%R) (op1 := +%R))
            /= ?mul0r //; last by move => /= x y; rewrite mulrDl.
    rewrite (big_mkcond ch) -big_split /=.
    apply big_rec2 => // i x y _ ->; rewrite ffunE.
    have ->: ((if ch i then cs i else 0) = cs i * ch i)%R by
      case: (ch i); rewrite ?mulr1 ?mulr0.
    by rewrite -mulrA -mulrDr addnC PoszD PoszM.
Qed.

End automata_construction.
