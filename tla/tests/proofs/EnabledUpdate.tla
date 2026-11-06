---- MODULE EnabledUpdate ----
EXTENDS TLAPS
VARIABLES x, y
vars == <<x, y>>
A == x = FALSE /\ x' = TRUE /\ UNCHANGED y
THEOREM x = FALSE => ENABLED <<A>>_vars
BY ExpandENABLED DEF A, vars
====
