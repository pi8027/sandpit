Require Import Coq.Strings.String.

Goal False.
  let s := eval lazy in (String "254" "test" ++ String "255" "")%string in
    idtac s.
Abort.
