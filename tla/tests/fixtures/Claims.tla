---- MODULE Claims ----
EXTENDS Integers
CONSTANT N
ASSUME Positive == N > 0
THEOREM Claim == N + 1 > 0
PROOF OBVIOUS
====
