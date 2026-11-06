---- MODULE FalseEnabledNext ----
EXTENDS TLAPS
VARIABLE x, y
vars == <<x, y>>
A == /\ x = FALSE /\ x' = TRUE /\ UNCHANGED y
THEOREM x = TRUE => ENABLED <<A>>_vars
  BY ExpandENABLED DEF A, vars
====
