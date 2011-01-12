
sum([],0).
sum([X|XS],R) :- sum(XS,TS) , R is X+TS.

