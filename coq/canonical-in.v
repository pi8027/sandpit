Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Section SeqElem.

Variable (T : eqType).

Structure tagged_seq := Tag { untag :> seq T }.

Structure seqElem (x : T) :=
  SeqElem { seqElem_seq : tagged_seq;
            seqElemProof : x \in untag seqElem_seq }.

Definition appr_tag s := Tag s.
Definition appl_tag s := appr_tag s.
Definition consr_tag s := appl_tag s.
Canonical consl_tag s := consr_tag s.

Lemma seqElem_consl_proof (x : T) (xs : tagged_seq) : x \in (x :: xs).
  by rewrite in_cons; apply/orP; left; apply/eqP.
Qed.

Canonical seqElem_consl (x : T) (xs : tagged_seq) : seqElem x :=
  SeqElem x (consl_tag (x :: xs)) (seqElem_consl_proof x xs).

Lemma seqElem_consr_proof (x x' : T) (xs : seqElem x) :
  x \in (x' :: seqElem_seq x xs).
Proof.
  by rewrite in_cons; apply/orP; right; case: xs.
Qed.

Canonical seqElem_consr (x x' : T) (xs : seqElem x) : seqElem x :=
  SeqElem x (consr_tag (x' :: seqElem_seq x xs)) (seqElem_consr_proof x x' xs).

Lemma seqElem_appl_proof (x : T) (l : seqElem x) (r : seq T) :
  x \in (seqElem_seq x l ++ r).
Proof.
  by rewrite mem_cat; apply/orP; left; case: l.
Qed.

Canonical seqElem_appl (x : T) (l : seqElem x) (r : seq T) : seqElem x :=
  SeqElem x (appl_tag (seqElem_seq x l ++ r)) (seqElem_appl_proof x l r).

Lemma seqElem_appr_proof (x : T) (l : seq T) (r : seqElem x) :
  x \in (l ++ seqElem_seq x r).
Proof.
  by rewrite mem_cat; apply/orP; right; case: r.
Qed.

Canonical seqElem_appr (x : T) (l : seq T) (r : seqElem x) : seqElem x :=
  SeqElem x (appr_tag (l ++ seqElem_seq x r)) (seqElem_appr_proof x l r).

End SeqElem.

Goal forall n, 1 \in ((3 :: nseq n n) ++ [:: 2; 1] ++ nseq n n).
move => n; apply seqElemProof.
Qed.
