(*
(add-to-list 'coq-load-path "~/src/coq/regular/")
*)

Require Import
  ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple finfun div
  bigop ssralg ssrnum ssrint dfa_to_re regexp automata.
Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* term and formula of Presburger arithmetic *)

Inductive term (v : nat) :=
  | t_const of nat
  | t_var   of 'I_v
  | t_add   of term v & term v
  | t_mulc  of nat & term v.

Inductive formula (v : nat) :=
  | f_all    of formula v.+1
  | f_exists of formula v.+1
  | f_neg    of formula v
  | f_and    of formula v & formula v
  | f_or     of formula v & formula v
  | f_leq    of term v & term v.

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

Fixpoint term_val v (t : term v) (i : nat ^ v) : nat :=
  match t with
    | t_const n => n
    | t_var v => i v
    | t_add t t' => term_val t i + term_val t' i
    | t_mulc n t => n * term_val t i
  end.

Fixpoint formula_semantics v (f : formula v) : nat ^ v -> Prop :=
  match f with
    | f_all f =>
      fun i => forall n : nat, formula_semantics f (cons_tuple n i)
    | f_exists f =>
      fun i => exists n : nat, formula_semantics f (cons_tuple n i)
    | f_neg f => fun i => ~ formula_semantics f i
    | f_and f f' => fun i => formula_semantics f i /\ formula_semantics f' i
    | f_or f f' => fun i => formula_semantics f i \/ formula_semantics f' i
    | f_leq t t' => fun i =>  term_val t i <= term_val t' i
  end.

Fixpoint nformula_semantics v (f : nformula v) : nat ^ v -> Prop :=
  match f with
    | nf_exists f =>
      fun i => exists n : nat, nformula_semantics f (cons_tuple n i)
    | nf_neg f => fun i => ~ nformula_semantics f i
    | nf_or f f' => fun i => nformula_semantics f i \/ nformula_semantics f' i
    | nf_atomic t n => fun i => (\sum_(m < v) t m * i m <= n)%R
  end.

(* normal form computation *)

Fixpoint normal_t v (t : term v) : int ^ v * int :=
  match t with
    | t_const n => ([ffun _ => 0%R], (n : int))
    | t_var var => ([ffun var' => (var == var' : int)], 0%R)
    | t_add t t' =>
      let: (c, n) := normal_t t in
      let: (c', m) := normal_t t' in
      ([ffun var => c var + c' var], n + m)%R
    | t_mulc c t =>
      let: (c', n) := normal_t t in
      ([ffun var => (c : int) * c' var], (c : int) * n)%R
  end.

Fixpoint normal_f v (f : formula v) : nformula v :=
  match f with
    | f_all f => nf_neg (nf_exists (nf_neg (normal_f f)))
    | f_exists f => nf_exists (normal_f f)
    | f_neg f => nf_neg (normal_f f)
    | f_and f f' => nf_neg (nf_or (nf_neg (normal_f f)) (nf_neg (normal_f f')))
    | f_or f f' => nf_or (normal_f f) (normal_f f')
    | f_leq t t' =>
      let: (c, n) := normal_t t in
      let: (c', m) := normal_t t' in
      nf_atomic [ffun var => c var - c' var]%R (m - n)%R
  end.

(* correctness proof *)

Lemma nt_correctness v (t : term v) i :
  (term_val t i : int) =
  (let (c, n) := normal_t t in \sum_(m < v) c m * i m + n)%R.
Proof.
  elim: t i => /=.
  - move => n i; rewrite -{1}(add0r (n : int)); f_equal.
    apply big_ind => //.
    + by move => x y <- <-.
    + by move => ? _; rewrite ffunE mul0r.
  - move => var i; rewrite addr0.
    rewrite (bigID (eq_op^~ var)) /= -{1}(addr0 (i var : int)); f_equal.
    + by rewrite big_pred1_eq ffunE eqxx mul1r.
    + apply big_ind => //.
      * by move => x y <- <-.
      * by move => ? /negPf; rewrite ffunE eq_sym => -> /=; rewrite mul0r.
  - move => t; case_eq (normal_t t) => c n _ IHt.
    move => t'; case_eq (normal_t t') => c' m _ IHt' i.
    rewrite PoszD IHt IHt' !addrA (addrAC _ n); do 2 f_equal.
    by rewrite -big_split /=; apply eq_big => // var _; rewrite ffunE mulrDl.
  - move => n t; case_eq (normal_t t) => c m H IH i.
    rewrite PoszM IH mulrDr big_distrr /=.
    by f_equal; apply eq_big => // var _; rewrite ffunE mulrA.
Qed.

Lemma nf_correctness v (f : formula v) i :
  (forall v (f : nformula v) i,
    let P := nformula_semantics f i in ~ ~ P -> P) ->
  (formula_semantics f i <-> nformula_semantics (normal_f f) i).
Proof.
  move => dne; move: v f i; refine (formula_ind _ _ _ _ _ _) => /=.
  - move => v f IH i; split => H.
    + by case => n; apply; apply IH, H.
    + by move => n; apply IH, dne => H0; apply H; exists n.
  - by move => v f IH i; split; case => n H; exists n; apply IH.
  - by move => v f IH i; split => H H0; apply H, IH.
  - move => v f IHf f' IHf' i; split.
    + by case => H H0 []; apply; [apply IHf | apply IHf'].
    + by move => H; split; [apply IHf | apply IHf'];
        apply dne => H'; apply H; [left | right].
  - by move => v f IHf f' IHf' i; split;
      (case => H; [left; apply IHf | right; apply IHf']).
  - move => v t t' i; rewrite -lez_nat !nt_correctness.
    case_eq (normal_t t); case_eq (normal_t t') => /= c n _ c' m _.
    rewrite -ler_subr_addr -addrA addrC -ler_subl_addr
      (@big_morph _ _ -%R%R 0%R _ 0%R _ (@opprD _)) ?oppr0 // -big_split /=.
    set x := BigOp.bigop _ _ _; set y := BigOp.bigop _ _ _.
    suff ->: x = y by []; rewrite {}/x {}/y.
    by apply eq_big => // var _; rewrite ffunE mulrDl mulNr.
Qed.

(* automata construction *)

Section Range.

Variable (i k : int).

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
