---- MODULE CaseReferences ----
THEOREM ASSUME NEW P PROVE P \/ ~P
<1>1. CASE P
  <2>1. USE <1>1
  <2>2. QED OBVIOUS
<1>2. CASE ~P
  <2>1. USE <1>2
  <2>2. QED OBVIOUS
<1>3. USE <1>1, <1>2
<1>4. QED OBVIOUS
====
