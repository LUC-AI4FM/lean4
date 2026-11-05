---- MODULE HigherRecursive ----
EXTENDS Naturals
RECURSIVE Fold(_, _, _)
Fold(Op(_,_), value, count) ==
  IF count = 0 THEN value ELSE Fold(Op, Op(value, 1), count - 1)
Zero == Fold(+, 7, 0)
RECURSIVE Base(_, _)
Base(Op(_,_), value) == IF TRUE THEN Op(value, value) ELSE Base(Op, value)
BaseLaw == Base(+, 2) = 4
====
