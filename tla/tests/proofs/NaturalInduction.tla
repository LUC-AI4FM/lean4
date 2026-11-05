---- MODULE NaturalInduction ----
EXTENDS Integers
THEOREM ASSUME NEW P(_), P(0), \A n \in Nat : P(n) => P(n+1)
        PROVE \A n \in Nat : P(n)
OBVIOUS
====
