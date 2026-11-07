---- MODULE FalseInstanceArithmetic ----
EXTENDS Naturals
VARIABLE z
---- MODULE Inner ----
EXTENDS Naturals
VARIABLE v
Two == 1 + 1
====
I == INSTANCE Inner WITH v <- z
\* Naturals defines a + b == {a, b} as a placeholder; under that body
\* 1 + 1 = {1}. The built-in meaning must be used, so this is rejected.
THEOREM I!Two = {1} BY DEF I!Two
====
