---- MODULE Fairness ----
EXTENDS TLAPS
VARIABLE x
A == x' = ~x
THEOREM SF_x(A) => WF_x(A)
BY PTL DEF A
THEOREM WF_x(A) /\ []ENABLED <<A>>_x => []<><<A>>_x
BY PTL DEF A
====
