---- MODULE ValueForms ----
EXTENDS Integers
TupleBound == \A <<x,y>> \in {<<1,2>>, <<3,4>>} : x < y
Functions == [x,y \in 1..3 |-> x + y]
Applied == Functions[1,2]
Cases == CASE 1 < 0 -> 1 [] 2 > 0 -> 2 [] OTHER -> 3
Products == {1, TRUE} \X {"a", <<2>>}
f[x \in 1..3] == x+1
ShortForm == f[1]
====
