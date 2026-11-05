---- MODULE StandardLibrary ----
EXTENDS Integers, Sequences, Bags
Positive(x) == x > 0
Selected == SelectSeq(<<-1, 0, 1, 2>>, Positive)
Bag == SetToBag({1,2})
Count == BagCardinality(Bag)
Copies == CopiesIn(1, Bag)
Joined == Bag (+) Bag
Filtered == BagOfAll(Positive, Bag)
====
