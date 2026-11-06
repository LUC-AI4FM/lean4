---- MODULE FalseWeakFairnessRank ----
(* Fairness on the wrong action: only B is fair, so x need never become TRUE. *)
EXTENDS TLAPS
VARIABLE x, y
vars == <<x, y>>
Init == x = FALSE /\ y = FALSE
A == x = FALSE /\ y = TRUE /\ x' = TRUE /\ y' = y
B == y = FALSE /\ y' = TRUE /\ x' = x
Next == A \/ B
Spec == Init /\ [][Next]_vars /\ WF_vars(B)
TypeOK == x \in BOOLEAN /\ y \in BOOLEAN
LEMMA TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK' BY DEF TypeOK, Next, vars, A, B
<1>. QED BY <1>1, <1>2, PTL DEF Spec
THEOREM Spec => <>(x = TRUE)
<1>1. TypeOK /\ ~(x = TRUE) => ENABLED <<Next>>_vars
  BY ExpandENABLED DEF TypeOK, Next, A, B, vars
<1>2. TypeOK /\ ~(x = TRUE) /\ (y = TRUE) /\ <<Next>>_vars => (x = TRUE)'
  BY DEF TypeOK, Next, A, B, vars
<1>3. TypeOK /\ ~(x = TRUE) /\ ~(y = TRUE) /\ <<Next>>_vars => (y = TRUE)'
  BY DEF TypeOK, Next, A, B, vars
<1>4. TypeOK /\ (y = TRUE) /\ [Next]_vars => (y = TRUE)'
  BY DEF TypeOK, Next, A, B, vars
<1>. QED BY TypeCorrect, <1>1, <1>2, <1>3, <1>4, PTL DEF Spec
====
