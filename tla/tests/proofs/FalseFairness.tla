---- MODULE FalseFairness ----
EXTENDS TLAPS
VARIABLE x
A == x' = ~x
THEOREM []ENABLED <<A>>_x => []<><<A>>_x
BY PTL DEF A
====
