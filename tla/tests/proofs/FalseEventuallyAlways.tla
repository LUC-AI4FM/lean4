---- MODULE FalseEventuallyAlways ----
(* x toggles forever: []<>(x = TRUE) holds, <>[](x = TRUE) does not. *)
EXTENDS TLAPS
VARIABLE x
Init == x = FALSE
Next == x' = ~x
Spec == Init /\ [][Next]_x /\ WF_x(Next)
THEOREM Spec => <>[](x = TRUE)
BY PTL DEF Spec, Init, Next
====
