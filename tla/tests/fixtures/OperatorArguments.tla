---- MODULE OperatorArguments ----
EXTENDS Integers
Apply(Op(_,_), x, y) == Op(x,y)
Plus == Apply(+, 2, 3)
Intersection == Apply(\cap, {1,2}, {2,3})
Union == Apply(\cup, {1}, {2})
Equals == Apply(=, 1, 1)
PlusLaw == Plus = 5
IntersectionLaw == 2 \in Intersection
====
