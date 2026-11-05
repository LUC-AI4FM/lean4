---- MODULE Counter ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x + 1
Inv == x >= 0
Spec == Init /\ [][Next]_x
====
