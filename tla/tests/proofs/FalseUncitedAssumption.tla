---- MODULE FalseUncitedAssumption ----
CONSTANTS x, S
ASSUME Ax == x \in S
THEOREM x \in S OBVIOUS
====
