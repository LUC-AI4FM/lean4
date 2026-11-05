---- MODULE Names ----
Value == 1
Behavior == 2
Constants == 3
truth == Value = 1
integer == 4
Nat == 5
TLAProofClaim0 == 6
THEOREM TRUE
PROOF OBVIOUS
True == TRUE
False == FALSE
b(v) == v
c(v) == b(v)
n(v) == c(v)
LocalNames == n(1) = 1
====
