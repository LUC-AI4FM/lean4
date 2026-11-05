---- MODULE SequenceOperations ----
EXTENDS Integers, Sequences
S == <<1, TRUE, "x">>
Length == Len(S)
Appended == Append(S, FALSE)
Concatenated == S \o <<2>>
First == Head(S)
Rest == Tail(S)
Slice == SubSeq(S, 2, 3)
Space == Seq({1, TRUE, "x"})
LengthLaw == Length = 3
FirstLaw == First = 1
====
