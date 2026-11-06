---- MODULE NaturalSubtraction ----
EXTENDS Naturals
VARIABLES x, y
THEOREM ASSUME x \in Nat, y \in Nat, x < y PROVE y - x \in Nat
OBVIOUS
THEOREM ASSUME x \in Nat \ {0}, y \in Nat \ {0}, x < y PROVE y - x \in Nat \ {0}
OBVIOUS
====
