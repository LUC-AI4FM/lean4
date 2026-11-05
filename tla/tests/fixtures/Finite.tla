---- MODULE Finite ----
EXTENDS Integers, FiniteSets
Mixed == {1, TRUE, "hello", <<2, FALSE>>}
Finite == IsFiniteSet(Mixed)
Count == Cardinality(Mixed)
Power == 2 ^ 10
====
