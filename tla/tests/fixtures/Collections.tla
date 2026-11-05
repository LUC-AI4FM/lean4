---- MODULE Collections ----
EXTENDS Integers, Sequences
CONSTANT N
VARIABLE x
Double(a) == a + a
Domain == {i \in 1..N : i % 2 = 0}
Mapped == {Double(i) : i \in Domain}
Func == [i \in Domain |-> Double(i)]
Bound == \A i \in Domain : i >= 0
Chosen == CHOOSE i \in Domain : i > 0
Local == LET F(a) == a + 1 IN F(N)
Init == x = 0
Inc == x' = IF x < N THEN x + 1 ELSE 0
Next == Inc \/ UNCHANGED x
Spec == Init /\ [][Next]_x /\ WF_x(Next)
Live == [](x >= 0) /\ <>(x = N)
====
