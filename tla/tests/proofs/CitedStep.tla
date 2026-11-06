---- MODULE CitedStep ----
CONSTANT x
D == x \in {x}
THEOREM D
<1>1. D BY DEF D
<1>2. D BY <1>1
<1> USE <1>2
<1> QED OBVIOUS
====
