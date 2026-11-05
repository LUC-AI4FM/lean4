---- MODULE TheoremArgument ----
---- MODULE Proof ----
CONSTANT x
THEOREM Fact == x = x
====
I(v) == INSTANCE Proof WITH x <- v
Apply(Op(_), x) == Op(x)
Law == Apply(I!Fact, 3)
====
