---- MODULE Recursive ----
EXTENDS Integers
RECURSIVE Fact(_), Sum(_,_), Impossible(_)
Fact(n) == IF n = 0 THEN 1 ELSE n * Fact(n-1)
Sum(m,n) == IF m = 0 THEN n ELSE Sum(m-1,n+1)
Impossible(x) == CHOOSE y : y /= Impossible(x)
f[n \in Nat] == IF n = 0 THEN 1 ELSE n*f[n-1]
Answer == Fact(5)
PairAnswer == Sum(2,3)
FunctionAnswer == f[5]
====
