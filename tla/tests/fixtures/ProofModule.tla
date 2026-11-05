---- MODULE ProofModule ----
CONSTANT c
THEOREM Fact == ASSUME NEW x PROVE c = c /\ x = x
PROOF OBVIOUS
====
