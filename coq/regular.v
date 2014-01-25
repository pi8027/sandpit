Require Import
  ssreflect ssrfun ssrbool eqtype ssrnat seq path choice fintype fingraph finfun
  bigop finset.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section regular.

Variable (Sigma : finType).

Record DFA := {
  DFA_states    : finType ;
  DFA_start     : DFA_states ;
  DFA_accept    : {set DFA_states} ;
  DFA_delta     : {ffun DFA_states -> {ffun Sigma -> DFA_states}} }.

Record NFA := {
  NFA_states    : finType ;
  NFA_start     : NFA_states ;
  NFA_accept    : {set NFA_states} ;
  NFA_delta     : {ffun NFA_states -> {ffun Sigma -> {set NFA_states}}} }.

Record eNFA := {
  eNFA_states   : finType ;
  eNFA_start    : eNFA_states ;
  eNFA_accept   : {set eNFA_states} ;
  eNFA_epsilon  : {ffun eNFA_states -> {set eNFA_states}} ;
  eNFA_delta    : {ffun eNFA_states -> {ffun Sigma -> {set eNFA_states}}} }.

Inductive RE : Type :=
  | re_emptyset
  | re_singleton of Sigma
  | re_concat of RE & RE
  | re_union of RE & RE
  | re_star of RE.

Section DFA.

Variable (dfa dfa' : DFA).

Definition DFA_delta' (xs : seq Sigma) (q : DFA_states dfa) : DFA_states dfa :=
  foldl (fun_of_fin (DFA_delta dfa)) q xs.

Definition DFA_match (xs : seq Sigma) : bool :=
  DFA_delta' xs (DFA_start dfa) \in DFA_accept dfa.

Definition NFA_of_DFA : NFA :=
  Build_NFA
    (DFA_start dfa)
    (DFA_accept dfa)
    [ffun q => [ffun x => [set DFA_delta dfa q x]]].

Definition DFA_reverse : eNFA :=
  @Build_eNFA
    (option_finType (DFA_states dfa))
    None
    [set Some (DFA_start dfa)]
    [ffun q => if q is None then (@Some _) @: DFA_accept dfa else set0]
    [ffun q => [ffun x =>
      [set Some q' | q' in [pred q' | Some (DFA_delta dfa q' x) == q]]]].

Definition DFA_complement : DFA :=
  Build_DFA (DFA_start dfa) (~: DFA_accept dfa) (DFA_delta dfa).

Definition DFA_intersection : DFA :=
  @Build_DFA
    (prod_finType (DFA_states dfa) (DFA_states dfa'))
    (DFA_start dfa, DFA_start dfa')
    [set (q, q') | q in DFA_accept dfa, q' in DFA_accept dfa']
    [ffun q => [ffun x => (DFA_delta dfa q.1 x, DFA_delta dfa' q.2 x)]].

End DFA.

Section NFA.

Variable (nfa : NFA).

Definition NFA_delta'
  (xs : seq Sigma) (qs : {set NFA_states nfa}) : {set NFA_states nfa} :=
  @foldl _ {set NFA_states nfa}
    (fun qs' x => cover [set NFA_delta nfa q x | q in qs'])
    qs xs.

Definition NFA_match (xs : seq Sigma) : bool :=
  NFA_accept nfa :&: NFA_delta' xs [set NFA_start nfa] != set0.

Definition eNFA_of_NFA : eNFA :=
  Build_eNFA (NFA_start nfa) (NFA_accept nfa) [ffun q => set0] (NFA_delta nfa).

Definition subset_construction_next qs x :=
  cover [set NFA_delta nfa q x | q in pred_of_set qs].

Definition subset_construction_filter : pred {set NFA_states nfa} :=
  connect
    (fun q1 q2 => q2 \in [set subset_construction_next q1 x | x in Sigma])
    [set NFA_start nfa].

Lemma subset_construction_next_proof (qs : {set NFA_states nfa}) x :
  subset_construction_filter qs ->
  subset_construction_filter (subset_construction_next qs x).
Proof.
  case/connectP => path1 H H0; apply/connectP.
  exists (path1 ++ [:: subset_construction_next qs x]).
  - by rewrite cat_path H /= andbT -H0; apply/imsetP; exists x.
  - by rewrite last_cat.
Qed.

Definition DFA_of_NFA : DFA :=
  @Build_DFA
    [finType of {qs : {set NFA_states nfa} | subset_construction_filter qs}]
    (exist subset_construction_filter [set NFA_start nfa] (connect0 _ _))
    [set st | sval st :&: NFA_accept nfa != set0]
    [ffun qs => [ffun x => exist subset_construction_filter
     (subset_construction_next (sval qs) x)
     (subset_construction_next_proof _ (proj2_sig qs))]].

End NFA.

Section eNFA.

Variable (enfa : eNFA).

Definition eclose (q : eNFA_states enfa) : {set eNFA_states enfa} :=
  [set q' | connect (fun x y => y \in eNFA_epsilon enfa x) q q'].

Definition eNFA_delta'
  (xs : seq Sigma) (qs : {set eNFA_states enfa}) : {set eNFA_states enfa} :=
  @foldl _ {set eNFA_states enfa}
    (fun qs' x => cover (eclose @: cover [set eNFA_delta enfa q x | q in qs']))
    qs xs.

Definition eNFA_match (xs : seq Sigma) : bool :=
  eNFA_accept enfa :&: eNFA_delta' xs (eclose (eNFA_start enfa)) != set0.

Definition subset_construction_next' qs x :=
  cover (eclose @: cover [set eNFA_delta enfa q x | q in pred_of_set qs]).

Definition subset_construction_filter' : pred {set eNFA_states enfa} :=
  connect
    (fun q1 q2 : {set eNFA_states enfa} =>
      q2 \in (subset_construction_next' q1 @: setT))
    (cover (eclose @: [set eNFA_start enfa])).

Lemma subset_construction_next_proof' (qs : {set eNFA_states enfa}) x :
  subset_construction_filter' qs ->
  subset_construction_filter' (subset_construction_next' qs x).
Proof.
  case/connectP => path1 H H0; apply/connectP.
  exists (path1 ++ [:: subset_construction_next' qs x]).
  - by rewrite cat_path H /= andbT -H0; apply/imsetP; exists x.
  - by rewrite last_cat.
Qed.

Definition DFA_of_eNFA :=
  @Build_DFA
    [finType of {qs : {set eNFA_states enfa} | subset_construction_filter' qs}]
    (exist subset_construction_filter'
     (cover (eclose @: [set eNFA_start enfa])) (connect0 _ _))
    [set st | sval st :&: eNFA_accept enfa != set0]
    [ffun qs => [ffun x => exist subset_construction_filter'
     (subset_construction_next' (sval qs) x)
     (subset_construction_next_proof' _ (proj2_sig qs))]].

End eNFA.

Definition regular_language (P : seq Sigma -> Prop) : Prop :=
  exists dfa, forall xs, DFA_match dfa xs <-> P xs.

Lemma NFA_of_DFA_eq dfa xs q :
  [set @DFA_delta' dfa xs q] = @NFA_delta' (NFA_of_DFA dfa) xs [set q].
Proof.
  rewrite /NFA_of_DFA /NFA_delta' /DFA_delta' /=.
  elim: xs q => //= x xs IH q.
  rewrite IH; f_equal.
  apply setP => q'; rewrite inE cover_imset; apply/esym/bigcupP; case: ifP.
  - by move/eqP => -> {q'}; exists q; rewrite ?ffunE inE.
  - by move/eqP => H H0; apply: H; case: H0 => q''; rewrite inE;
      move/eqP => H; subst q''; rewrite !ffunE inE; move/eqP.
Qed.

Lemma DFA_reverse_correct dfa xs (qs : {set DFA_states dfa}) :
  @eNFA_delta' (DFA_reverse dfa) (rev xs) [set Some q | q in qs] =
  [set Some q | q in predT & @DFA_delta' dfa xs q \in qs].
Proof.
  rewrite /DFA_reverse /eNFA_delta' /DFA_delta' /=.
  elim: xs qs => /= [| x xs IH] qs.
  - apply setP => q; apply/imsetP; case: ifP.
    + by case/imsetP => q'; rewrite inE => H H0; subst q; exists q'.
    + by move/negP => H H0; apply: H; case: H0 => q' H H0; subst q;
        apply/imsetP; exists q' => //; rewrite inE.
  - rewrite rev_cons -cats1 foldl_cat /= {}IH cover_imset.
    apply setP => q; apply/bigcupP; case: ifP.
    + case/imsetP => q'; rewrite inE => H H0; subst q; exists (Some q').
      * rewrite cover_imset; apply/bigcupP; exists (Some (DFA_delta dfa q' x)).
        - by apply/imsetP; exists (DFA_delta dfa q' x) => //; rewrite inE.
        - by rewrite !ffunE; apply/imsetP; exists q' => //; rewrite inE.
      * by rewrite /eclose /= inE connect0.
    + move/negP => H H0; apply: H; case: H0 => q'; rewrite cover_imset;
        case/bigcupP => q''; rewrite !ffunE; case/imsetP => q''';
        rewrite inE => H H0; subst q''; case/imsetP => q''; rewrite inE;
        case/eqP => H0 H1; subst q''' q'; rewrite /eclose /= inE;
        case/connectP; case; last by move => ? ? /=; rewrite ffunE inE.
      by move => /= _ H0; subst q; apply/imsetP; exists q'' => //; rewrite inE.
Qed.

Lemma DFA_complement_correct dfa xs :
  DFA_match dfa xs != DFA_match (DFA_complement dfa) xs.
Proof. by rewrite /DFA_match /DFA_complement negb_eqb inE addbN addbb. Qed.

Lemma DFA_intersection_correct dfa dfa' xs :
  DFA_match dfa xs && DFA_match dfa' xs =
  DFA_match (DFA_intersection dfa dfa') xs.
Proof.
  rewrite /DFA_intersection /DFA_match /DFA_delta' /=.
  elim: xs (DFA_start dfa) (DFA_start dfa') => /=.
  - move => q q'; apply/esym/imset2P; case: ifP.
    + by case/andP => H H0; apply: (Imset2spec H H0 erefl).
    + by move/negP => H H0; apply: H;
        case: H0 => q'' q''' H H0 [H1 H2]; subst; rewrite H H0.
  - by move => x xs IH qs qs'; rewrite !ffunE /= -IH.
Qed.

Lemma eNFA_of_NFA_eq nfa xs qs :
  @NFA_delta' nfa xs qs = @eNFA_delta' (eNFA_of_NFA nfa) xs qs.
Proof.
  elim: xs qs => //= x xs IH qs; rewrite {}IH; f_equal.
  apply/esym/setP; rewrite cover_imset => q; apply/bigcupP; case: ifP.
  - by move => H; exists q => //; rewrite /eclose /= inE connect0.
  - move/negP => H H0; apply: H; case: H0 => q' H; rewrite /eclose /= inE;
      case/connectP; case; last by move => ? ? /=; rewrite ffunE inE.
    by move => /= _ H0; subst q'.
Qed.

Lemma DFA_of_NFA_eq nfa xs (qs : {qs | subset_construction_filter qs}) :
  @NFA_delta' nfa xs (sval qs) = sval (@DFA_delta' (DFA_of_NFA nfa) xs qs).
Proof. by elim: xs qs => //= x xs IH [qs H] /=; rewrite !ffunE /= -IH. Qed.

Lemma DFA_of_eNFA_eq enfa xs (qs : {qs | subset_construction_filter' qs}) :
  @eNFA_delta' enfa xs (sval qs) = sval (@DFA_delta' (DFA_of_eNFA enfa) xs qs).
Proof. by elim: xs qs => //= x xs IH [qs H] /=; rewrite !ffunE /= -IH /=. Qed.

Definition DFA_minimization dfa : DFA :=
  DFA_of_eNFA (DFA_reverse (DFA_of_eNFA (DFA_reverse dfa))).

End regular.
