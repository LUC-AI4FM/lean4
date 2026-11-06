---- MODULE ModuleContext ----
CONSTANTS x, S
ASSUME Ax == x \in S
D == x \in {x}
USE DEF D
THEOREM D OBVIOUS
THEOREM x \in S BY Ax
USE Ax
THEOREM x \in S OBVIOUS
====
