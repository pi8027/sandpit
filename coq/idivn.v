Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.div.

Lemma divn_eq0 m n : (m %/ n == 0) = (n == 0) || (m < n).
Proof.
  case: (ltnP m n).
  - by move => H; rewrite orbT divn_small.
  - move => H; move/subnKC: (H) => <-.
    rewrite orbF -{1}(mul1n n).
    case: n H.
    - by move => _; rewrite divn0.
    - by move => n; rewrite divnMDl.
Qed.

Fixpoint iedivn_rec (d m n : nat) : nat * nat :=
  match d with
    | 0 => (0, m)
    | d'.+1 =>
      match edivn m n with
        | (m', 0) =>
          let (x, y) := iedivn_rec d' m' n in (x.+1, y)
        | _ => (0, m)
      end
  end.

Definition iedivn m n := nosimpl (iedivn_rec m) m n.

Definition idivn m n := fst (iedivn m n).

Definition imodn m n := snd (iedivn m n).

Lemma iedivn_recdepth d d' m n :
  m < n ^ d -> m < n ^ d' -> 0 < m -> iedivn_rec d m n = iedivn_rec d' m n.
Proof.
  elim: d d' m => //=.
  - by rewrite expn0 => d' [].
  - move => d IH [].
    - by rewrite expn0 => [[]].
    - move => d' m /=.
      rewrite edivn_def !expnS.
      case: (eqVneq (m %% n) 0).
      - move => H; rewrite H.
        move/eqP/divnK: (H) => {1 2}<-; rewrite mulnC.
        rewrite !ltn_mul2l; case/andP => H0 H1; case/andP => _ H2 H3.
        rewrite (IH d') // divn_gt0 //.
        move/eqP in H; apply (dvdn_leq H3 H).
      - by rewrite -lt0n; move/prednK => <- /=.
Qed.

Lemma iedivn_recdepth' d d' m n :
  m <= d -> m <= d' -> 0 < m -> 1 < n -> iedivn_rec d m n = iedivn_rec d' m n.
Proof.
  by move => *; apply iedivn_recdepth => //;
    (apply leq_trans with (n ^ m); [ apply ltn_expl | rewrite leq_exp2l]).
Qed.

Lemma iedivnE m n : iedivn m n = (idivn m n, imodn m n).
Proof. by rewrite /idivn /imodn; case: (iedivn m n). Qed.

Lemma iedivnE' m n : m = imodn m n * n ^ idivn m n.
Proof.
  rewrite /imodn /idivn /iedivn /=.
  move: {2 4}m => d.
  elim: d m.
  - by move => m; rewrite /= expn0 muln1.
  - move => /= d IH m.
    rewrite edivn_def.
    case: (eqVneq (m %% n) 0).
    - move => H; rewrite H.
      move/eqP/divnK: H => {1}<-.
      rewrite {1}(IH (m %/ n)).
      case: (iedivn_rec _ _ _) => /= x y.
      by rewrite expnSr mulnA.
    - rewrite -lt0n.
      move/prednK => <- /=.
      by rewrite expn0 muln1.
Qed.

Lemma idiv0n n : idivn 0 n = 0.
Proof. done. Qed.

Lemma imod0n n : imodn 0 n = 0.
Proof. done. Qed.

Lemma idivn0 n : idivn n 0 = 0.
Proof. by case: n. Qed.

Lemma imodn0 n : imodn n 0 = n.
Proof. by case: n. Qed.

Lemma idiv1n n : 1 < n -> idivn 1 n = 0.
Proof. by rewrite /idivn /iedivn /= edivn_def; move: n => [] // []. Qed.

Lemma imod1n n : imodn 1 n = 1.
Proof. by rewrite /imodn /iedivn /= edivn_def; move: n => [] // []. Qed.

Lemma idivn1 n : idivn n 1 = n.
Proof.
  rewrite /idivn /iedivn.
  elim: {1 3}n => //= n'.
  rewrite edivn_def modn1 divn1 /=.
  by case: iedivn_rec => //= a _ ->.
Qed.

Lemma imodn1 n : imodn n 1 = n.
Proof.
  rewrite /imodn /iedivn.
  elim: {1}n => //= n'.
  rewrite edivn_def modn1 divn1 /=.
  by case: iedivn_rec.
Qed.

Lemma idivnn n : 0 < n -> idivn n n = 1.
Proof.
  by move: n => [] // [] // n; rewrite /idivn /iedivn /= !edivn_def modnn divnn.
Qed.

Lemma imodnn n : 0 < n -> imodn n n = 1.
Proof.
  by move: n => [] // [] // n; rewrite /imodn /iedivn /= !edivn_def modnn divnn.
Qed.

Lemma idivn_eq0 m n : (idivn m n == 0) = ~~ (n %| m) || (m == 0).
Proof.
  rewrite /idivn /iedivn /dvdn.
  case: m => /=; first by rewrite eqxx orbT.
  move => m; rewrite edivn_def.
  by case: (m.+1 %% n) => //; case: iedivn_rec.
Qed.

Lemma idivn_muln m n : 0 < m -> 1 < n -> idivn (n * m) n = (idivn m n).+1.
Proof.
  move => H H0.
  rewrite /idivn /iedivn (iedivn_recdepth (n * m) m.+1 (n * m) n) /=.
  - by rewrite edivn_def modnMr mulKn ?(ltnW H0) //; case: iedivn_rec.
  - by apply ltn_expl.
  - by rewrite expnS ltn_mul2l (ltnW H0) /=; apply ltn_expl.
  - by rewrite muln_gt0 H (ltnW H0).
Qed.

Lemma idivn_dvdn m n : 0 < m -> 1 < n -> n %| m -> idivn m n = (idivn (m %/ n) n).+1.
Proof.
  rewrite dvdn_eq mulnC => H H0 H1.
  move/eqP: H1 H => {1 2}<-.
  rewrite muln_gt0; case/andP => _ H1.
  by apply idivn_muln.
Qed.

Lemma idivn_ndvdn m n : ~~ (n %| m) -> idivn m n = 0.
Proof. by move => H; apply/eqP; rewrite idivn_eq0 H. Qed.

Lemma expn_idivnl m n : 1 < n -> idivn (n ^ m) n = m.
Proof.
  move => H.
  elim: m => //=.
  - by rewrite expn0 idiv1n.
  - by move => m IH; rewrite expnS idivn_muln // ?IH // expn_gt0 (ltnW H).
Qed.

Lemma expn_idivnr m n e : 1 < n -> 0 < e -> idivn m (n ^ e) = idivn m n %/ e.
Proof.
  move => H H0.
  move: (@erefl _ (idivn m (n ^ e))).
  move: {1 3}(idivn _ _) => x.
  elim: x m.
  - move => m.
    case: e H0 => // e _.
    move/esym/eqP; rewrite idivn_eq0; case/orP.
    - move => H0; apply/esym/eqP; rewrite divn_eq0 eq_sym /= ltnS.
      elim: e m H0.
      - by move => m; rewrite expn1; move/idivn_ndvdn => ->.
      - move => e IH [| m]; first by rewrite idiv0n.
        case (eqVneq (n %| m.+1) true) => H0.
        - move/divnK: (H0) => <-.
          rewrite  mulnC expnS dvdn_pmul2l ?(ltnW H) ?idivn_muln //.
          - by apply IH.
          - by rewrite divn_gt0 ?(ltnW H) //; apply dvdn_leq.
        - by rewrite eq_sym negb_eqb /= in H0; rewrite idivn_ndvdn.
    - by move/eqP => ->; rewrite idiv0n div0n.
  - move => x IH m.
    case (eqVneq (n ^ e %| m) true).
    - admit.
    - by rewrite eq_sym negb_eqb /=; move/idivn_ndvdn => ->.
Qed.

Lemma idivn_spec (m n r : nat) :
  0 < m -> 1 < n -> (idivn m n == r) = (n ^ r %| m) && ~~(n ^ r.+1 %| m).
Proof.
  elim: r m.
  - by case => // m _; rewrite expn0 expn1 dvd1n idivn_eq0 /= orbC.
  - move => r IH m H H0.
    rewrite 2!(expnS n).
    case: (eqVneq (n %| m) true).
    - move => H1.
      have H2: 0 < m %/ n by rewrite divn_gt0 ?(ltnW H0) // dvdn_leq.
      move/divnK: H1; rewrite mulnC => <-.
      rewrite idivn_muln // eqSS.
      do 2 rewrite dvdn_pmul2l ?(ltnW H0) //.
      by apply IH.
    - rewrite eq_sym negb_eqb /= => H1.
      apply negb_inj; rewrite negb_and idivn_ndvdn //=.
      apply/esym/orP; left.
      apply/negP => H2; move/divnK: H2 H1 => <-; move/negP; apply.
      rewrite mulnCA; apply dvdn_mulr, dvdnn.
Qed.
