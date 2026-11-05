---- MODULE LibraryFunctions ----
EXTENDS Integers, TLC, Sequences
Mapping == ("a" :> 1) @@ ("b" :> 2)
Chosen == RandomElement({1})
Sorted == SortSeq(<<2,1>>, LAMBDA a,b : a <= b)
Perms == Permutations({1,2})
====
