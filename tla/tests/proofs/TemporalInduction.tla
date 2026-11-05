---- MODULE TemporalInduction ----
VARIABLE x
Init == x = 0
Next == x' = x
Inv == x = 0
THEOREM Init /\ [][Next]_x => []Inv
<1>1. Init => Inv BY DEF Init, Inv
<1>2. Inv /\ Next => Inv' BY DEF Inv, Next
<1>3. QED BY <1>1, <1>2 DEF Init, Next, Inv
====
