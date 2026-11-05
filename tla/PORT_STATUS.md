# TLA+ port acceptance record

Objective: existing `.tla` modules and Lean-native specifications share faithful
semantics, with checked proofs, reference compatibility tests and published code.
The integer/action milestone is not completion.

Baseline: b51ae21; seven translator tests and two counter proofs. Native temporal
semantics include stuttering, invariant induction and fairness. Source frontend is
handwritten and limited to integer variables; no source correspondence theorem.

Acceptance gates (all required):
- Source grammar and level checking, bindings, imports and INSTANCE substitutions.
- Untyped values, booleans, arithmetic, sets, functions, records and sequences.
- Quantification, CHOOSE, LET, operator parameters and recursion.
- Actions, priming, ENABLED, frames, temporal operators, fairness and hiding.
- Standard modules and proof obligations without accepting unproved theorems.
- Lean-native APIs for the same semantics and end-to-end proof examples.
- Reference-tool differential tests, negative/soundness tests, clean CI and push.

Current frontier: official SANY semantic XML frontend versus expanding handwritten
syntax. SANY has native grammar/level/module resolution, so test that interface
first. Exporter limitations must produce explicit diagnostics, never placeholders.

Verification: bounded library/proof checks on the coordinator; sustained builds
and larger corpus work require an authorized LUC host or public GitHub CI.
No new paid resources. No delegated agents or persistent remote workloads.

Next: pin reference tools; import and validate the SANY graph; replace textual
operator handling with resolved bindings; expand semantic coverage with tests.

Checkpoint after baseline:
- Official SANY 1.7.4 frontend pinned by SHA-256, resolved UIDs and module graph.
- Replaced handwritten CLI parser with the resolved compiler.
- Added typed collection/function native semantics and source compilation.
- 17 tests plus native/data/source proof checks pass on Lean 4.33.1/Python 3.11.
- Reference exporter level-error exit-zero regression caught and rejected.
- ASSUME/THEOREM are rejected pending obligation support, never silently dropped.

Open acceptance gates remain open. In particular typed source compilation is not
universal untyped TLA+ semantics. Next: source records/updates and obligation
handling; reference-tool differential checks; universal-value design. No delegated
agents or remote jobs. Only task-owned .tools and .lake caches are retained for
verification. The working checkout remains the active implementation directory.
