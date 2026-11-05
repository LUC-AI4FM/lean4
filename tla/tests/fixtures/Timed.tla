---- MODULE Timed ----
EXTENDS RealTime
VARIABLE x
Init == x = 0 /\ now = 0
Next == x' = x + 1 /\ UNCHANGED now
Clock == RTnow(x)
Bound == RTBound(Next, x, 1, 2)
Spec == Init /\ [][Next]_<<x, now>> /\ Clock /\ Bound
====
