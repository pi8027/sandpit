
typing([[V, TY] | _], vari(V), TY).
typing([[V2, _] | E], vari(V), TY) :- typing(E, vari(V), TY), V \= V2.
typing(E, app(T1, T2), TY) :- typing(E, T1, fun(TY2, TY)), typing(E, T2, TY2).
typing(E, lam(V, T), fun(TY1, TY2)) :- typing([[V, TY1] | E], T, TY2).

