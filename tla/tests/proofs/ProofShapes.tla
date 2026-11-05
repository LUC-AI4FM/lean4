---- MODULE ProofShapes ----
THEOREM Reflexive == \A x : x = x
<1>1. TAKE x
<1>2. QED OBVIOUS
THEOREM Existential == \E x : x = x
<1>1. WITNESS TRUE
<1>2. QED OBVIOUS
THEOREM Choice == (\E x : x = x) => TRUE
<1>1. SUFFICES ASSUME \E x : x = x PROVE TRUE OBVIOUS
<1>2. PICK x : x = x OBVIOUS
<1>3. HAVE x = x
<1>4. QED OBVIOUS
THEOREM Cases == TRUE
<1>1. CASE TRUE
  OBVIOUS
<1>2. QED BY <1>1
====
