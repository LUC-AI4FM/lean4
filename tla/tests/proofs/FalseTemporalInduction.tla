---- MODULE FalseTemporalInduction ----
VARIABLE x
Init == x = 0
Next == x' = 1
Inv == x = 0
THEOREM Init /\ [][Next]_x => []Inv
<1>1. Init => Inv BY DEF Init, Inv
<1>2. QED BY <1>1 DEF Init, Next, Inv
====
