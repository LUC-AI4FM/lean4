---- MODULE FactScope ----
CONSTANT x
D == x \in {x}
THEOREM Base == D
<1>1. D BY DEF D
<1> HIDE <1>1
<1> QED BY <1>1
THEOREM D
<1>1. D BY DEF D
<1> HIDE <1>1
<1> USE <1>1
<1> QED OBVIOUS
THEOREM D
<1> HIDE Base
<1> QED BY Base
====
