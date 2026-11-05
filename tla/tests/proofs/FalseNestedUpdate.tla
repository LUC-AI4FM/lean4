---- MODULE FalseNestedUpdate ----
EXTENDS Integers
f == [x \in {1} |-> [y \in {2} |-> 3]]
t == [f EXCEPT ![1][2] = 1, ![1][2] = @ + 1]
THEOREM t[1][2] = 1
BY DEF t, f
====
