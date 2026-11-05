---- MODULE Temporal ----
EXTENDS Integers
VARIABLE x
Step == x' = x + 1
Twice == Step \cdot Step
Progress == (x = 0) ~> (x = 1)
Hidden == \EE y : [](y = x)
Nested == \EE y : \EE z : [](y = x /\ z = y)
Universal == \AA y : [](y = y)
====
