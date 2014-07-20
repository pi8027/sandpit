(*
やりたいこと:
Coq でマージソートを余計なパラメータもパラメータが減ることの証明も無しで書く。
方針:
Coq の termination checker が通すような書き方をする。
*)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section mergesort.

Variables (A : Type) (cmp : A -> A -> bool).

(*
とりあえず普通の方法で書いてみる。
*)
Fixpoint merge xs :=
  match xs with
    | [::] => id
    | x :: xs' =>
      fix merge' ys {struct ys} :=
        if ys is y :: ys'
          then if cmp x y then x :: merge xs' ys else y :: merge' ys'
          else xs
  end.

Fixpoint merge_pair xs :=
  match xs with
    | [::] => [::]
    | [:: x] => [:: x]
    | (x :: x' :: xs) => merge x x' :: merge_pair xs
  end.

Fixpoint mergesort' xs n :=
  match n with
    | 0 => [::]
    | S n =>
      match xs with
        | [:: x] => x
        | _ => mergesort' (merge_pair xs) n
      end
  end.

Definition mergesort (xs : seq A) : seq A :=
  mergesort' (map (fun x => [:: x]) xs) (size xs).

Lemma merge_pair_decreasing xs : size (merge_pair xs) <= size xs.
Proof.
  by move: xs; fix IH 1; case => //= _ [] //= _ xs; rewrite ltnS; apply leqW.
Qed.

(*
sorted の証明
*)
Fixpoint sorted' x xs :=
  if xs is x' :: xs then cmp x x' && sorted' x' xs else true.

Definition sorted xs :=
  if xs is x :: xs then sorted' x xs else true.

Lemma sortedE x xs : sorted (x :: xs) =
  (if xs is x' :: _ then cmp x x' else true) && sorted xs.
Proof. by case: xs. Qed.

Theorem mergesort_sorted (xs : seq A) :
  (forall x y, ~ cmp x y -> cmp y x) -> sorted (mergesort xs).
Proof.
  rewrite /mergesort => asym.
  set xs' := map _ _.
  have H: all sorted xs' by rewrite {}/xs'; elim: xs.
  have H0: size xs' <= size xs by rewrite /xs' size_map.
  elim: {xs} (size xs) xs' H0 H => //= n IH [].
  - by move => _ _; apply IH.
  - move => x [] //; first by move => _ /andP [].
    move => x' xs H H0; apply: IH;
      first by rewrite /=; apply leq_ltn_trans with (size xs) => //;
                 apply merge_pair_decreasing.
    move: H0; rewrite -/(merge_pair (x :: x' :: xs)).
    move: {n x x' xs H} [:: _, _ & _].
    fix IH 1.
    case => // x [] //= x' xs /and3P [H H0 H1]; apply/andP; split.
    + elim: x x' H H0 {xs H1} => // x xs IHx; elim => // y ys IHy H H0 /=.
      case: ifP => H1.
      * move: H; rewrite !sortedE => /andP [H2 H3]; apply/andP; split.
        - by case: xs H2 {IHx IHy H3} => //= x' xs H2; case: ifP.
        - by apply IHx.
      * move: H0; rewrite !sortedE; case/andP => H2 H3; apply/andP; split.
        - case: ys H2 {IHx IHy H3} => //.
          + by move => _; apply asym; rewrite H1.
          + by move => y' ys H2; case: ifP => // _; apply asym; rewrite H1.
        - by apply IHy.
    + by apply IH.
Qed.

(*
permutation の証明
*)
Inductive permutation : seq A -> seq A -> Prop :=
  | perm_id    : forall xs, permutation xs xs
  | perm_swap  : forall x x' xs, permutation (x :: x' :: xs) (x' :: x :: xs)
  | perm_cons  : forall x xs ys,
                 permutation xs ys -> permutation (x :: xs) (x :: ys)
  | perm_trans : forall xs ys zs,
                 permutation xs ys -> permutation ys zs -> permutation xs zs.

Hint Constructors permutation.

Lemma perm_cat xsl xsr ysl ysr :
  permutation xsl ysl -> permutation xsr ysr ->
  permutation (xsl ++ xsr) (ysl ++ ysr).
Proof.
  move => H H0; apply perm_trans with (xsl ++ ysr).
  - by elim: xsl {H} => //= x xsl H; constructor.
  - move: xsl ysl H {xsr H0}.
    refine (permutation_ind _ _ _ _) => //=; auto.
    by move => xs ys zs H H0 H1 H2; apply perm_trans with (ys ++ ysr).
Qed.

Lemma perm_sym xs ys : permutation xs ys -> permutation ys xs.
  move: xs ys; refine (permutation_ind _ _ _ _) => //=.
  - by move => x xs ys _ H; constructor.
  - by move => xs ys zs _ H _ H0; apply perm_trans with ys.
Qed.

Lemma perm_catC xs ys : permutation (xs ++ ys) (ys ++ xs).
Proof.
  elim: xs ys => //=; first by move => ys; rewrite cats0.
  move => x xs IHx; elim; first by rewrite cats0.
  move => /= y ys IHy.
  apply perm_trans with (x :: y :: ys ++ xs);
    first by constructor; apply (IHx (y :: ys)).
  apply perm_trans with (y :: x :: xs ++ ys); last by constructor.
  apply perm_trans with (x :: y :: xs ++ ys); do ?constructor.
  apply perm_sym, IHx.
Qed.

Theorem mergesort_perm (xs : seq A) : permutation xs (mergesort xs).
Proof.
  rewrite /mergesort.
  set xs' := map _ _.
  have {1}->: xs = flatten xs' by rewrite {}/xs'; elim: xs => //= x xs {1}->.
  have H0: size xs' <= size xs by rewrite /xs' size_map.
  elim: {xs} (size xs) xs' H0; first by case => //= _.
  move => n IH []; first by move => _ /=; elim: n {IH} => //=.
  move => x xs; rewrite /size ltnS -/size; case: xs => //;
    first by rewrite /= cats0.
  move => x' xs H.
  apply perm_trans with (flatten (merge_pair (x :: x' :: xs)));
    last by apply IH => /=; apply leq_ltn_trans with (size xs) => //;
            apply merge_pair_decreasing.
  move: {n x x' xs IH H} [:: _, _ & _].
  fix IH 1.
  case => //= x [] //= x' xs; rewrite catA; apply perm_cat; last by apply IH.
  elim: x x' {xs IH} => // x xs IHx; elim; first by rewrite cats0.
  move => y ys IHy /=; case: ifP => _.
  - constructor; apply IHx.
  - apply perm_trans with (y :: ys ++ x :: xs);
      first by apply (perm_catC (x :: xs)).
    constructor; apply perm_trans with (x :: xs ++ ys);
      [apply perm_catC | apply IHy].
Qed.

End mergesort.

Section mergesort2.

Variables (A : Type) (cmp : A -> A -> bool).

(*
いきなりマージソートを書くのは面倒なので、とりあえずツリーを作ってみる。マージソー
トは、このツリーの構造に沿ってやれば良いはずなのでこれができれば十分なはず。
*)
Inductive tree := B of tree & tree | L of A.

(*
1. Coq が seq2tree_s xs l ≼ xs と認識してくれるように書きたい。
   (参考: http://coq.inria.fr/files/coq5-slides-sacchini.pdf)
2. 本当は seq2tree_s と seq2tree_t は組を返す単一の関数にしたいが、そうしてしまう
   と現状の termination checker はどうやっても1に書いたようなことを認識できない。
   いつでも定義をマージできるように、同じ構造の再帰で書く。
*)
Fixpoint seq2tree_s (xs : seq A) (l : nat) : seq A :=
  if l is S l'
    then
      if seq2tree_s xs l' is _ :: xs'
        then seq2tree_s xs' l'
        else xs
    else xs.

Fixpoint seq2tree_t (x : A) (xs : seq A) (l : nat) : tree :=
  if l is S l'
    then
      if seq2tree_s xs l'  is x' :: xs'
        then B (seq2tree_t x xs l') (seq2tree_t x' xs' l')
        else seq2tree_t x xs l'
    else L x.

Fixpoint seq2tree' (t : tree) (xs : seq A) (l : nat) : tree :=
  if xs is x' :: xs'
    then
      seq2tree'
        (B t (seq2tree_t x' xs' l))
        (drop (2 ^ l - 1) xs') (* (seq2tree_s xs' l) *) (S l)
    else t. (* drop (2 ^ l - 1) xs' ≺ x' :: xs' ≡ xs *)
(*
Linear sized type (c.f. http://dx.doi.org/10.1007/978-3-319-07151-0_11) が導入され
ると seq2tree_s xs' l ≺ x' :: xs' ≡ xs も分かるだろうか。
*)

Definition seq2tree (xs : seq A) : option tree :=
  if xs is x :: xs'
    then Some (seq2tree' (L x) xs' 0)
    else None.



End mergesort2.

Eval compute in seq2tree (iota 0 11).
Eval compute in (mergesort leq [:: 9; 3; 6; 2; 10; 0; 4; 7; 1; 8; 5]).