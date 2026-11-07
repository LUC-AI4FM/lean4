---- MODULE WeakFairnessInfinitely ----
EXTENDS Naturals, TLAPS
VARIABLE x
Init == x = 0
Next == x' = x + 1
Spec == Init /\ [][Next]_x /\ WF_x(Next)
Inv == x \in Nat
THEOREM Spec => []<><<Next>>_x
<1>1. Spec => []Inv
  <2>1. Init => Inv BY DEF Init, Inv
  <2>2. Inv /\ [Next]_x => Inv' BY DEF Inv, Next
  <2>. QED BY <2>1, <2>2, PTL DEF Spec
<1>2. ASSUME Inv PROVE ENABLED <<Next>>_x
  BY ExpandENABLED DEF Next, Inv
<1>3. ASSUME []Inv PROVE WF_x(Next) => []<><<Next>>_x
  BY <1>2, PTL
<1>. QED BY <1>1, <1>3 DEF Spec
====
