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

Fixpoint merge xs :=
  match xs with
    | [::] => id
    | x :: xs' =>
      fix merge' ys {struct ys} :=
        if ys is y :: ys'
          then if cmp x y then x :: merge xs' ys else y :: merge' ys'
          else xs
  end.

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



End mergesort.

Eval compute in seq2tree (iota 0 11).
