---- MODULE Records ----
EXTENDS Integers, Sequences
Original == [count |-> 1, items |-> <<2, 3>>]
Changed == [Original EXCEPT !.count = @ + 1, !.items[2] = @ + 4]
Repeated == [Original EXCEPT !.count = @ + 1, !.count = @ + 2]
Good == Changed.count = 2 /\ Changed.items[2] = 7 /\ Repeated.count = 4
RecordSet == [count : {1, 2}, items : {<<2, 3>>}]
Included == Original \in RecordSet
Function == [i \in 1..3 |-> i * 2]
Updated == [Function EXCEPT ![2] = @ + 1]
UpdateGood == Updated[2] = 5 /\ Updated[1] = 2
====
