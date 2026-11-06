---- MODULE FalsePTLInvariant ----
(* x = 0 initially but is not preserved by Next. *)
EXTENDS Integers, TLAPS
VARIABLE x
Init == x = 0
Next == x' = x + 1
THEOREM Init /\ [][Next]_x => [](x = 0)
BY PTL DEF Init, Next
====
