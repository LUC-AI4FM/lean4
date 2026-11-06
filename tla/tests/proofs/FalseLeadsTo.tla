---- MODULE FalseLeadsTo ----
EXTENDS Integers, TLAPS
CONSTANT N
ASSUME NAssumption == N \in Nat
VARIABLE x
Next == x' = x + 1
Live == [](x \in Nat) /\ [][Next]_x
THEOREM Progress == Live /\ <>(x = N) => <>(x = N + 1)
<1>1. ASSUME x \in Nat PROVE ENABLED <<Next>>_x
  BY <1>1, ExpandENABLED DEF Next
<1>2. ASSUME x = N /\ <<Next>>_x PROVE (x = N + 1)'
  BY <1>2 DEF Next
<1>3. ASSUME x = N /\ [Next]_x PROVE (x = N)' \/ (x = N + 1)'
  BY <1>3 DEF Next
<1> QED BY <1>1, <1>2, <1>3, PTL DEF Live
====
