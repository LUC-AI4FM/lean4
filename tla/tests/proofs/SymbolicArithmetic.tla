---- MODULE SymbolicArithmetic ----
EXTENDS Integers
THEOREM \A n \in Nat : n + 1 > n OBVIOUS
THEOREM \A m, n \in Int : m <= n => m + 1 <= n + 1 OBVIOUS
THEOREM ASSUME NEW m \in Int, NEW n \in Int, n > 0
        PROVE (m % n) \in 0..(n-1)
OBVIOUS
====
