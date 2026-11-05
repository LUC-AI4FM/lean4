---- MODULE NestedModules ----
EXTENDS Integers
VARIABLE x
---- MODULE Arithmetic ----
CONSTANT k, Op(_)
Value(a) == Op(a) + k
====
---- MODULE Action ----
VARIABLE y
Step == y' = y + 1
====
Double(a) == a + a
I(v) == INSTANCE Arithmetic WITH k <- v, Op <- Double
J == INSTANCE Action WITH y <- x
Answer == I(2)!Value(3)
Next == J!Step
====
