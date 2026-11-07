---- MODULE FalseSpecEquivalence ----
EXTENDS Naturals, TLAPS
VARIABLE x
\* The initial conditions differ; equal next-state relations do not help.
Init1 == x = 0
Init2 == x = 1
Next == x' = x + 1
Spec1 == Init1 /\ [][Next]_x
Spec2 == Init2 /\ [][Next]_x
THEOREM Spec1 <=> Spec2
<1>1. [Next]_x <=> [Next]_x OBVIOUS
<1>. QED BY <1>1, PTL DEF Spec1, Spec2
====
