---- MODULE NestedCalls ----
EXTENDS Integers
Answer == LET F(x) == x + 1 IN F(F(1))
Higher == LET H(Op(_), x) == Op(x)
              Inc(x) == x + 1
          IN H(LAMBDA k : H(Inc, k), 1)
====
