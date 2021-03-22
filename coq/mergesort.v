From mathcomp Require Import all_ssreflect.
Declare ML Module "paramcoq".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac destruct_reflexivity := 
  intros ; repeat match goal with 
    | [ x : _ |- _ = _ ] => destruct x; reflexivity; fail
  end.

Ltac destruct_construct x := 
    (destruct x; [ constructor 1 ]; auto; fail)
 || (destruct x; [ constructor 1 | constructor 2 ]; auto; fail)
 || (destruct x; [ constructor 1 | constructor 2 | constructor 3]; auto; fail).

Ltac unfold_cofix := intros; match goal with 
 [ |- _ = ?folded ] =>  
    let x := fresh "x" in 
    let typ := type of folded in 
    (match folded with _ _ => pattern folded | _ => pattern folded at 2 end);
    match goal with [ |- ?P ?x ] => 
    refine (let rebuild : typ -> typ := _ in 
            let path : rebuild folded = folded := _ in  
            eq_rect _ P _ folded path) end; 
    [ intro x ; destruct_construct x; fail 
    | destruct folded; reflexivity
    | reflexivity]; fail
end.

Ltac destruct_with_nat_arg_pattern x :=
  pattern x;
  match type of x with 
   | ?I 0 => refine (let gen : forall m (q : I m), 
     (match m return I m -> Type with 
         0 => fun p => _ p
     | S n => fun _  => unit end q) := _ in gen 0 x)     
   | ?I (S ?n) => refine (let gen : forall m (q : I m), 
     (match m return I m -> Type with 
         0 => fun _  => unit 
     | S n => fun p => _ p end q) := _ in gen (S n) x)
  end; intros m q; destruct q.

Ltac destruct_reflexivity_with_nat_arg_pattern := 
  intros ; repeat match goal with 
    | [ x : _ |- _ = _ ] => destruct_with_nat_arg_pattern x; reflexivity; fail
  end.
 
Global Parametricity Tactic := ((destruct_reflexivity; fail)
                            || (unfold_cofix; fail) 
                            || (destruct_reflexivity_with_nat_arg_pattern; fail)
                            ||  auto).

Parametricity bool.
Parametricity list.

Lemma bool_R_refl b1 b2 : b1 = b2 -> bool_R b1 b2.
Proof. by case: b1 => <-; constructor. Qed.

Lemma map_rel_map A B (f : A -> B) (l : seq A) :
  list_R (fun x y => f x = y) l (map f l).
Proof. by elim: l; constructor. Qed.

Lemma rel_map_map A B (f : A -> B) (l : seq A) (fl : seq B) :
  list_R (fun x y => f x = y) l fl -> fl = map f l.
Proof. by elim/list_R_ind: l fl / => //= ? ? <- ? ? _ ->. Qed.

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
  let inner_rec := fix inner_rec mode acc x s :=
    if s is y :: s then
      if eqb (leT x y) mode then
        inner_rec mode (x :: acc) y s
      else
        let stack := merge_sort_push (condrev mode (x :: acc)) stack in
        merge_sort_rec stack y s
    else
      merge_sort_pop (condrev mode (x :: acc)) stack
  in
  if s is y :: s then
    inner_rec (leT x y) [:: x] y s else merge_sort_pop [:: x] stack.

Definition sort s := if s is x :: s then merge_sort_rec [::] x s else [::].

End SortSeq.

Parametricity Recursive sort.

Lemma map_sort (T T' : Type) (f : T' -> T) (leT' : rel T') (leT : rel T) :
  {mono f : x y / leT' x y >-> leT x y} ->
  {morph map f : s1 / sort leT' s1 >-> sort leT s1}.
Proof.
move=> leT_mono xs; apply/esym/rel_map_map/sort_R/map_rel_map.
by move=> ? ? <- ? ? <-; apply/bool_R_refl/esym/leT_mono.
Qed.

Lemma sort_map (T T' : Type) (f : T' -> T) (leT : rel T) (s : seq T') :
  sort leT (map f s) = map f (sort (relpre f leT) s).
Proof. exact/esym/map_sort. Qed.

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

Fixpoint merge_sort_rec (stack : seq (seq T)) (x : T) (s : seq T) : seq T :=
  let inner_rec := fix inner_rec mode acc x s :=
    if s is y :: s then
      if eqb (leT x y) mode then
        inner_rec mode (x :: acc) y s
      else
        let stack := merge_sort_push (condrev mode (x :: acc)) stack false in
        merge_sort_rec stack y s
    else
      merge_sort_pop (condrev mode (x :: acc)) stack false
  in
  if s is y :: s then
    inner_rec (leT x y) [:: x] y s else merge_sort_pop [:: x] stack false.

Definition sort s : seq T :=
  if s is x :: s then merge_sort_rec [::] x s else [::].

End SortSeq.

Parametricity Recursive sort.

Lemma map_sort (T T' : Type) (f : T' -> T) (leT' : rel T') (leT : rel T) :
  {mono f : x y / leT' x y >-> leT x y} ->
  {morph map f : s1 / sort leT' s1 >-> sort leT s1}.
Proof.
move=> leT_mono xs; apply/esym/rel_map_map/sort_R/map_rel_map.
by move => ? ? <- ? ? <-; apply/bool_R_refl/esym/leT_mono.
Qed.

Lemma sort_map (T T' : Type) (f : T' -> T) (leT : rel T) (s : seq T') :
  sort leT (map f s) = map f (sort (relpre f leT) s).
Proof. exact/esym/map_sort. Qed.

End CBV.

From QuickChick Require Import QuickChick.
Set Warnings "-extraction-opaque-accessed,-extraction".

Definition sortP (s : list (nat * nat)) :=
  let leq' := relpre fst leq in
  (CBN.sort leq' s == sort leq' s) &&
  (CBV.sort leq' s == sort leq' s).

QuickChick sortP.
