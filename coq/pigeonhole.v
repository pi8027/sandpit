Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Lemma pigeonhole (S T : finType) (H : #|T| < #|S|) (f : S -> T) :
  exists i j : S, i != j /\ f i = f j.
Proof.
have {H} H: ~ injective f
  by move => H0; move: H; apply/negP; rewrite -leqNgt;
     rewrite -(card_imset _ H0) max_card.
suff: [exists i, (i.1 != i.2) && (f i.1 == f i.2)]
  by move/existsP => [[i j] /andP [H0 /eqP H1]]; exists i, j.
apply/negbNE/negP; rewrite negb_exists => /forallP H0; apply H => i j H1.
by move: (H0 (i, j)) => /=; rewrite H1 eqxx andbT negbK => /eqP.
Qed.
