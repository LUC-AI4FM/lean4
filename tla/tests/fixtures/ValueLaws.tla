---- MODULE ValueLaws ----
EXTENDS Integers
MixedMember == TRUE \in {1, TRUE, "x"}
TupleRead == <<1, TRUE, "x">>[2] = TRUE
Identity == [x \in {1,2} |-> x]
FunctionRead == Identity[1] = 1
====
