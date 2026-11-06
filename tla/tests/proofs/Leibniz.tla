---- MODULE Leibniz ----
EXTENDS Naturals
VARIABLE x
F(u) == {u, u + 1}
THEOREM ASSUME x = 1 PROVE F(x) = F(1)
OBVIOUS
====
