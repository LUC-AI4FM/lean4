---- MODULE HigherOrder ----
EXTENDS Integers
CONSTANT F(_)
Apply(Op(_), x) == Op(x)
Forward(Op(_), x) == Apply(Op,x)
Inc(x) == x+1
Answer == Forward(Inc,2)
ConstantCall == Forward(F,2)
====
