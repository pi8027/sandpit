Require Import Omega.

Notation minn x y := (x - (x - y)).

Lemma minnA x y z : minn x (minn y z) = minn (minn x y) z.
  omega.
Qed.
