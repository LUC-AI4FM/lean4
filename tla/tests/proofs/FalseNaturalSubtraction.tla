---- MODULE FalseNaturalSubtraction ----
EXTENDS Naturals
VARIABLES x, y
THEOREM ASSUME x \in Nat, y \in Nat, x <= y PROVE y - x \in Nat \ {0}
OBVIOUS
====
