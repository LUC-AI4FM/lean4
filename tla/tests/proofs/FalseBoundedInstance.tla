---- MODULE FalseBoundedInstance ----
CONSTANT Quorums
ASSUME QuorumAssumption == \A Q1, Q2 \in Quorums : Q1 \cup Q2 # {}
THEOREM \A Q \in Quorums : Q = {}
BY QuorumAssumption
====
