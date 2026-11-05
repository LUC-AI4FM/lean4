---- MODULE StructuredClaims ----
EXTENDS Integers
THEOREM ASSUME NEW x, x \in Int PROVE x = x
PROOF OBVIOUS
THEOREM ASSUME NEW x \in {1,2}, NEW F(_) PROVE F(x) = F(x)
PROOF OBVIOUS
====
