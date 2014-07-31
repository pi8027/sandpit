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
  if n is n.+1
    then (if xs is [:: x] then x else mergesort' (merge_pair xs) n)
    else [::].

Definition mergesort (xs : seq A) : seq A :=
  mergesort' (map (fun x => [:: x]) xs) (size xs).

Fixpoint list2_rec (A : Type) (P : seq A -> Set)
  (c1 : P [::]) (c2 : forall x, P [:: x])
  (c3 : forall x x' xs, P xs -> P [:: x, x' & xs]) (xs : seq A) : P xs :=
  match xs with
    | [::] => c1
    | [:: x] => c2 x
    | [:: x, x' & xs] => c3 x x' xs (list2_rec c1 c2 c3 xs)
  end.

Lemma merge_pair_decreasing xs : size (merge_pair xs) <= size xs.
Proof. by elim/list2_rec: xs => //= _ _ xs H; rewrite ltnS; apply leqW. Qed.

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
  elim: {xs} (size xs) xs' H0 H => //= n IH [];
    first by move => _ _; apply IH.
  move => x [] //; first by move => _ /andP [].
  move => x' xs H H0; apply: IH;
    first by rewrite /=; apply leq_ltn_trans with (size xs) => //;
               apply merge_pair_decreasing.
  move: H0; rewrite -/(merge_pair (x :: x' :: xs)).
  elim/list2_rec: {n x x' xs H} [:: _, _ & _] =>
    //= x x' xs IH /and3P [H H0 H1]; rewrite {}IH // andbT.
  elim: x x' H H0 {xs H1} => // x xs IHx;
    elim => // y ys IHy H H0 /=; case: ifP => H1.
  - move: H; rewrite !sortedE => /andP [H2 H3]; rewrite IHx // andbT.
    by case: xs H2 {IHx IHy H3} => //= x' xs; case: ifP.
  - move: H0; rewrite !sortedE; case/andP => H2 H3; rewrite IHy // andbT.
    case: ys H2 {IHx IHy H3} => //.
    + by move => _; apply asym; rewrite H1.
    + by move => y' ys; case: ifP => // _ _; apply asym; rewrite H1.
Qed.

End mergesort.

(*
permutation の証明
*)
Theorem mergesort_perm (A : eqType) (cmp : A -> A -> bool) (xs : seq A) :
  perm_eq xs (mergesort cmp xs).
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
  apply perm_eq_trans with (flatten (merge_pair cmp (x :: x' :: xs)));
    last by apply IH => /=; apply leq_ltn_trans with (size xs) => //;
            apply merge_pair_decreasing.
  elim/list2_rec: {n x x' xs IH H} [:: _, _ & _] => //= x x' xs; rewrite catA.
  rewrite -(perm_cat2l (x ++ x')); move/perm_eq_trans; apply; rewrite perm_cat2r.
  elim: x x' {xs} => // x xs IHx; elim; first by rewrite cats0.
  move => y ys IHy /=; case: ifP => _.
  - rewrite (perm_cat2l [:: x]); apply IHx.
  - move/perm_eqlP/perm_eq_trans: (perm_catCA (x :: xs) [:: y] ys); apply => /=.
    rewrite (perm_cat2l [:: y]); apply IHy.
Qed.

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
