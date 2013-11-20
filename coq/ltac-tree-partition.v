Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.seq.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition unit := True.

Lemma left_unit A : A <-> unit /\ A.
Proof. rewrite /unit; tauto. Qed.

Lemma right_unit A : A <-> A /\ unit.
Proof. rewrite /unit; tauto. Qed.

Lemma partitionL1 A Al Ar B Bl Br :
  (A <-> Al /\ Ar) -> (B <-> Bl /\ Br) -> (A /\ B <-> (Al /\ Bl) /\ (Ar /\ Br)).
Proof. tauto. Qed.

Lemma partitionL2 A A' B B' :
  (A <-> A') -> (B <-> B') -> (A /\ B <-> A' /\ B').
Proof. tauto. Qed.

Ltac decide_in x xs :=
  match xs with
    | x :: _ => constr: true
    | _ :: ?xs' => decide_in x xs'
    | nil => constr: false
  end.

Ltac partition xs P :=
  lazymatch P with
    | ?A /\ ?B =>
      let Ha := fresh "H" in
      let Hb := fresh "H" in
      partition xs A => Ha;
      partition xs B => Hb;
      match goal with
        | Ha : _ <-> ?Al /\ ?Ar, Hb : _ <-> ?Bl /\ ?Br |- _ =>
          let Hl := match constr: (Al, Bl) with
            | (unit, _) => constr: (iff_sym (left_unit Bl))
            | (_, unit) => constr: (iff_sym (right_unit Al))
            | _ => constr: (iff_refl (Al /\ Bl))
          end in
          let Hr := match constr: (Ar, Br) with
            | (unit, _) => constr: (iff_sym (left_unit Br))
            | (_, unit) => constr: (iff_sym (right_unit Ar))
            | _ => constr: (iff_refl (Ar /\ Br))
          end in
          move: (iff_trans (partitionL1 Ha Hb) (partitionL2 Hl Hr)) => {Ha Hb}
      end
    | ?X =>
      let inl := decide_in X xs in
      match inl with
        | true => move: (right_unit X)
        | false => move: (left_unit X)
      end
  end.

Goal False.
  move: True True True True True True True True => A B C D E F G H.
  partition [:: A; C; F] (A /\ (B /\ C /\ D) /\ E /\ (F /\ G) /\ H).
  move => _.
  partition [:: F; C; A] (A /\ (B /\ C /\ D) /\ E /\ (F /\ G) /\ H).
  move => _.
  partition [:: A; C; D; G] ((A /\ B /\ C) /\ D /\ (E /\ F /\ G) /\ H).
  move => _.
  partition [:: D; A; G; C] ((A /\ B /\ C) /\ D /\ (E /\ F /\ G) /\ H).
  move => _.
Abort.
