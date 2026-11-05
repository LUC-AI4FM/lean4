---- MODULE TupleBinders ----
THEOREM \A <<x, y>> \in {<<1, 2>>} : x = x
<1> TAKE <<x, y>> \in {<<1, 2>>}
<1> QED OBVIOUS
THEOREM ASSUME \E <<x, y>> \in {<<1, 2>>} : x = x PROVE TRUE
<1> PICK <<x, y>> \in {<<1, 2>>} : x = x OBVIOUS
<1> QED OBVIOUS
====
