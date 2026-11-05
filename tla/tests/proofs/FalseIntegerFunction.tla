---- MODULE FalseIntegerFunction ----
EXTENDS Integers
CONSTANT f
THEOREM f \in [{0} -> Int] => f[0] = 0
OBVIOUS
====
