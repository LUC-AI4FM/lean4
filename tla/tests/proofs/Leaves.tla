---- MODULE Leaves ----
CONSTANT p
ASSUME Premise == p = TRUE
Foo == 3
THEOREM Reflexive == \A x: x = x
OBVIOUS
THEOREM Given == p = TRUE
BY Premise
THEOREM Reused == p = TRUE
BY Given
THEOREM Expanded == Foo = 3
BY DEF Foo
THEOREM ASSUME NEW x PROVE x = x
OBVIOUS
====
