---- MODULE BoundedWitness ----
THEOREM \E x \in {1}, y \in {2} : x = 1 /\ y = 2
<1> WITNESS 1 \in {1}, 2 \in {2}
<1> QED OBVIOUS
THEOREM \E p : p = (1 \in {1})
<1> WITNESS 1 \in {1}
<1> QED OBVIOUS
====
