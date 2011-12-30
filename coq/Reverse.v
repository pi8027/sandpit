
Section List.

  Variables A : Type.

  Inductive list : Type :=
    | nil : list
    | cons : A -> list -> list.

  Fixpoint append (l1 l2 : list) : list :=
    match l1 with
      | nil => l2
      | cons x xs => cons x (append xs l2)
    end.

  Infix "++" := append (right associativity, at level 60).

  Fixpoint rev (l : list) : list :=
    match l with
      | nil => nil
      | cons x xs => rev xs ++ cons x nil
    end.

  Lemma append_id_left (l : list) : nil ++ l = l.
    auto.
  Qed.

  Lemma append_id_right (l : list) : l ++ nil = l.
    induction l.
    auto.
    simpl.
    apply (f_equal (cons a)).
    auto.
  Qed.

  Lemma append_comm (l1 l2 l3 : list) : l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
    induction l1.
    auto.
    simpl.
    apply (f_equal (cons a)).
    auto.
  Qed.

  Lemma app_rev_comm (l1 l2 : list) : rev (l1 ++ l2) = rev l2 ++ rev l1.
    induction l1.
    simpl.
    rewrite (append_id_right (rev l2)).
    auto.
    simpl.
    rewrite (append_comm (rev l2) (rev l1) (cons a nil)).
    apply (f_equal (fun l => l ++ cons a nil)).
    auto.
  Qed.

  Lemma rev_rev_id (l : list) : rev (rev l) = l.
    induction l.
    auto.
    simpl.
    rewrite (app_rev_comm (rev l) (cons a nil)).
    simpl.
    apply (f_equal (cons a)).
    auto.
  Qed.

End List.

