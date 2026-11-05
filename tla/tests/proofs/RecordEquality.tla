---- MODULE RecordEquality ----
THEOREM \A x, y : [a |-> x, b |-> y] = [b |-> y, a |-> x]
OBVIOUS
THEOREM \A x, y, p, q :
  ([a |-> x, b |-> y] = [b |-> q, a |-> p]) <=> (x = p /\ y = q)
OBVIOUS
====
