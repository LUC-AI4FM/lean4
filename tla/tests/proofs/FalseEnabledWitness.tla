---- MODULE FalseEnabledWitness ----
EXTENDS TLAPS
VARIABLE x
THEOREM ENABLED (x' = TRUE /\ x' = FALSE)
BY ExpandENABLED
====
