---- MODULE FalseWeakFairnessInfinitely ----
EXTENDS Naturals, TLAPS
VARIABLE x
\* Disabled once x reaches 5, so weak fairness forces no further steps.
Next == x < 5 /\ x' = x + 1
Inv == x \in Nat
THEOREM ASSUME []Inv PROVE WF_x(Next) => []<><<Next>>_x
  BY PTL DEF Next, Inv
====
