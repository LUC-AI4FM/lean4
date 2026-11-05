---- MODULE HigherRecursive ----
EXTENDS Naturals
RECURSIVE Fold(_, _, _)
Fold(Op(_,_), value, count) ==
  IF count = 0 THEN value ELSE Fold(Op, Op(value, 1), count - 1)
Zero == Fold(+, 7, 0)
RECURSIVE Base(_, _)
Base(Op(_,_), value) == IF TRUE THEN Op(value, value) ELSE Base(+, value)
BaseLaw == Base(+, 2) = 4
RECURSIVE Capture(_, _)
Capture(Op(_), count) ==
  IF count = 0 THEN Op(1)
  ELSE LET Shift(x) == Op(x) + count IN Capture(Shift, count - 1)
Captured == Capture(LAMBDA x: x, 2)
Apply(Op(_), value) == Op(value)
RECURSIVE Forwarded(_)
Forwarded(value) == IF TRUE THEN value ELSE Apply(Forwarded, value)
ForwardedLaw == Forwarded(3) = 3
====
