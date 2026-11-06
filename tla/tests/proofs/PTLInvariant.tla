---- MODULE PTLInvariant ----
EXTENDS Integers, TLAPS
VARIABLE x
Init == x = 0
Next == x' = x + 2
Inv == x \in Nat /\ x % 2 = 0
THEOREM Init /\ [][Next]_x => []Inv
<1>1. Init => Inv BY DEF Init, Inv
<1>2. Inv /\ [Next]_x => Inv' BY DEF Inv, Next
<1>. QED BY <1>1, <1>2, PTL
====
