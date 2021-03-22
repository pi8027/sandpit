From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition condrev (T : Type) (r : bool) (xs : seq T) : seq T :=
  if r then rev xs else xs.

Module CBN.

Section SortSeq.

Variables (T : Type) (leT : rel T).

Fixpoint merge_sort_push s stack :=
  match stack with
  | [::] :: stack' | [::] as stack' => s :: stack'
  | s' :: stack' => [::] :: merge_sort_push (merge leT s' s) stack'
  end.

Fixpoint merge_sort_pop s1 stack :=
  if stack is s2 :: stack' then merge_sort_pop (merge leT s2 s1) stack' else s1.

Fixpoint merge_sort_rec (stack : seq (seq T)) x s :=
  if s is y :: s then
    merge_sort_rec' stack (leT x y) [:: x] y s
  else
    merge_sort_pop [:: x] stack
with
merge_sort_rec' (stack : seq (seq T)) (mode : bool) acc x s :=
  if s is y :: s then
    if leT x y == mode then
      merge_sort_rec' stack mode (x :: acc) y s
    else
      let stack' := merge_sort_push (condrev mode (x :: acc)) stack in
      merge_sort_rec stack' y s
  else
    merge_sort_pop (condrev mode (x :: acc)) stack.

Definition sort s := if s is x :: s then merge_sort_rec [::] x s else [::].

End SortSeq.

End CBN.

Module CBV.

Section SortSeq.

Fixpoint revmerge T (leT : rel T) (xs : seq T) : seq T -> seq T -> seq T :=
  if xs is x :: xs'
  then fix revmerge' (ys acc : seq T) :=
         if ys is y :: ys'
         then if leT x y then
                revmerge leT xs' ys (x :: acc)
              else
                revmerge' ys' (y :: acc)
         else catrev xs acc
  else catrev.

Variables (T : Type) (leT : rel T).

Fixpoint merge_sort_push
         (xs : seq T) (stack : seq (seq T)) (mode : bool) : seq (seq T) :=
  match stack with
    | [::] :: stack' | [::] as stack' => xs :: stack'
    | ys :: stack =>
      let zs :=
          if mode then
            revmerge (fun x y => leT y x) xs ys [::]
          else
            revmerge leT ys xs [::]
      in
      [::] :: merge_sort_push zs stack (~~ mode)
  end.

Fixpoint merge_sort_pop
         (xs : seq T) (stack : seq (seq T)) (mode : bool) : seq T :=
  match stack with
    | [::] => if mode then rev xs else xs
    | [::] :: [::] :: stack => merge_sort_pop xs stack mode
    | [::] :: stack => merge_sort_pop (rev xs) stack (~~ mode)
    | ys :: stack =>
      let zs :=
          if mode then
            revmerge (fun x y => leT y x) xs ys [::]
          else
            revmerge leT ys xs [::]
      in
      merge_sort_pop zs stack (~~ mode)
  end.

Fixpoint merge_sort_rec (stack : seq (seq T)) x s :=
  if s is y :: s then
    merge_sort_rec' stack (leT x y) [:: x] y s
  else
    merge_sort_pop [:: x] stack false
with
merge_sort_rec' (stack : seq (seq T)) (mode : bool) acc x s :=
  if s is y :: s then
    if leT x y == mode then
      merge_sort_rec' stack mode (x :: acc) y s
    else
      let stack' := merge_sort_push (condrev mode (x :: acc)) stack false in
      merge_sort_rec stack' y s
  else
    merge_sort_pop (condrev mode (x :: acc)) stack false.
      
Definition sort s := if s is x :: s then merge_sort_rec [::] x s else [::].

End SortSeq.

End CBV.

From QuickChick Require Import QuickChick.
Set Warnings "-extraction-opaque-accessed,-extraction".

Definition sortP (s : list (nat * nat)) :=
  let leq' := relpre fst leq in
  (CBN.sort leq' s == sort leq' s) &&
  (CBV.sort leq' s == sort leq' s).

QuickChick sortP.
