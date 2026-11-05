---- MODULE FalseInduction ----
EXTENDS Integers
THEOREM ASSUME NEW P(_), \A n \in Nat : P(n) => P(n+1)
        PROVE \A n \in Nat : P(n)
OBVIOUS
====
