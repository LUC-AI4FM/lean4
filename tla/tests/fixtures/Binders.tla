---- MODULE Binders ----
EXTENDS Integers
All == \A x, y \in 1..3 : x + y >= 2
Some == \E x \in 1..3, y \in 2..4 : x = y
Sums == {x + y : x \in 1..3, y \in 2..4}
Member == 5 \in Sums
====
