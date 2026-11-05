---- MODULE Universal ----
EXTENDS Integers, Sequences
Mixed == {1, TRUE, "hello", <<2, FALSE>>}
HasBool == TRUE \in Mixed
AllReflexive == \A x : x = x
Witness == CHOOSE x : x = 1
Inc(a) == a + 1
Apply(F(_), x) == F(x)
Answer == Apply(Inc, 2)
====
