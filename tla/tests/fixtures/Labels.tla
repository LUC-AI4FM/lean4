---- MODULE Labels ----
EXTENDS Integers, Sequences
A(x) == foo :: x=x
B == A(1)!foo
C == \A x : bar(x) :: x=x
D == C!bar(2)
Plain == label :: TRUE
Selected == Plain!label
Filtered == SelectSeq(<<1,2>>, LAMBDA x : x > 1)
====
