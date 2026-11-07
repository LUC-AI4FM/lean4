---- MODULE InstanceArithmetic ----
EXTENDS Naturals
VARIABLE z
---- MODULE Inner ----
EXTENDS Naturals
VARIABLE v
Two == 1 + 1
Next == v' = (v + 1) % 2
====
I == INSTANCE Inner WITH v <- z
THEOREM I!Two = 2 BY DEF I!Two
THEOREM z = 1 /\ I!Next => z' = 0 BY DEF I!Next
====
