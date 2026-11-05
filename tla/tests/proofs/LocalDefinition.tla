---- MODULE LocalDefinition ----
THEOREM \A x : x = x
<1> TAKE x
<1> DEFINE Identity(y) == y
<1>1. Identity(x) = x OBVIOUS
<1> QED BY <1>1
====
