Require Import ssreflect seq ssrnat.

Set Implicit Arguments.

Axiom PrintAxiom : forall A, A -> Set.

Goal forall A (xs ys : seq A), PrintAxiom (xs ++ ys).
  move => A xs ys.
  replace (xs ++ ys) with (foldr cons [::] (xs ++ ys))
    by by move: (xs ++ ys) => {xs ys}; elim => //= x xs H; f_equal.
  rewrite foldr_cat.
  replace (foldr cons [::] ys) with ys by by elim: ys => //= y ys H; f_equal.
Abort.