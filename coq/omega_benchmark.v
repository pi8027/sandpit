Require Import Omega.

Notation minn x y := (x - (x - y)) (only parsing).

Lemma minnC x y : minn x y = minn y x.
Proof. Time omega. Time Qed.

Lemma minnC' x y : minn x y = minn (y - 0) (x - 0).
Proof. Time omega. Time Qed.

Lemma minnC'' x y : minn (x - 0) y = minn (y - 0) x.
Proof. Time omega. Time Qed.

Lemma minnA x y z : minn x (minn y z) = minn (minn x y) z.
Proof. Time omega. Time Qed.
