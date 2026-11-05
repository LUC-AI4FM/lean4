---- MODULE ArithmeticOperations ----
EXTENDS Integers
DivisionLaw == /\ 7 \div 2 = 3
               /\ (-7) \div 2 = -4
               /\ 7 % 2 = 1
               /\ (-7) % 2 = 1
====
