Require Import ssrbool ssrnat seq.

Set Implicit Arguments.

Fixpoint enth (A : Type) (xs : seq A) : forall n : nat, n < size xs -> A :=
  match xs return forall n, n < size xs -> A with
    | [::] => fun n H => False_rect A (Bool.diff_false_true H)
    | x :: xs => fun (n : nat) =>
      match n with
        | 0 => fun _ => x
        | n.+1 => enth xs n
      end
  end.