---- MODULE ExceptStep ----

EXTENDS TLAPS
CONSTANT P
VARIABLE st
TypeOK == st \in [P -> {"idle", "busy", "done", "failed"}]
Consistent == \A p, q \in P : ~(st[p] = "done" /\ st[q] = "failed")
Start(p) == st[p] = "idle" /\ st' = [st EXCEPT ![p] = "busy"]
Finish(p) == /\ st[p] = "busy" /\ (\A q \in P : st[q] # "failed")
             /\ st' = [st EXCEPT ![p] = "done"]
Fail(p) == /\ st[p] \in {"idle", "busy"} /\ (\A q \in P : st[q] # "done")
           /\ st' = [st EXCEPT ![p] = "failed"]
Next == \E p \in P : Start(p) \/ Finish(p) \/ Fail(p)
THEOREM TypeOK /\ Consistent /\ [Next]_st => (TypeOK /\ Consistent)'
BY DEF TypeOK, Consistent, Next, Start, Finish, Fail
====
