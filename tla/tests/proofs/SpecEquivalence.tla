---- MODULE SpecEquivalence ----
EXTENDS Naturals, TLAPS
VARIABLE x
Init1 == x = 0
Init2 == 0 = x
Next1 == x' = x + 1
Next2 == x + 1 = x' /\ TRUE
Spec1 == Init1 /\ [][Next1]_x
Spec2 == Init2 /\ [][Next2]_x
THEOREM Spec1 <=> Spec2
<1>1. Init1 <=> Init2 BY DEF Init1, Init2
<1>2. [Next1]_x <=> [Next2]_x BY DEF Next1, Next2
<1>. QED BY <1>1, <1>2, PTL DEF Spec1, Spec2
====
