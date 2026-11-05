---- MODULE InstanceBinding ----
VARIABLE z
---- MODULE Inner ----
VARIABLES x, y
A == x' = 0 /\ y' = 1
E == ENABLED A
====
I == INSTANCE Inner WITH x <- z, y <- z
THEOREM I!E BY DEF I!E
THEOREM ~ENABLED I!A BY DEF I!A
====
