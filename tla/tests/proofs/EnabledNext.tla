---- MODULE EnabledNext ----
EXTENDS TLAPS
VARIABLE x, y, flip
vars == <<x, y, flip>>
TypeOK == /\ x \in BOOLEAN /\ y \in BOOLEAN /\ flip \in BOOLEAN
A == /\ x = FALSE /\ x' = TRUE /\ UNCHANGED <<y, flip>>
B == /\ y = FALSE /\ y' = TRUE /\ flip' = ~flip /\ UNCHANGED x
C == /\ y = FALSE /\ y' = TRUE /\ flip' = ~flip /\ UNCHANGED x
Next == A \/ B \/ C
THEOREM TypeOK /\ ~(x = TRUE) => ENABLED <<Next>>_vars
  BY ExpandENABLED DEF TypeOK, Next, A, B, C, vars
====
