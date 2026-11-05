---- MODULE FalseStateGeneralization ----
VARIABLE x
THEOREM ASSUME x = 0 PROVE [](x = 0)
<1>1. x = 0 OBVIOUS
<1>2. QED BY <1>1
====
