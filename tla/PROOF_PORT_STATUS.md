# TLAPS proof-script port

Objective: unchanged TLAPS proof scripts produce proofs checked by Lean, with
positive and negative reference tests, complete language/backend coverage and
verified pushed changes. A leaf-only milestone is not completion.

Baseline: 9dae0d4 imports specifications and theorem obligations but does not
translate proof scripts. SANY already exports resolved proof trees. Heavy Lean
verification uses the existing public GitHub Actions workflow; the Mac performs
editing and bounded checks. No helpers or paid compute were started.

Acceptance gates:
- OBVIOUS, BY, ONLY, DEF and imported theorem reconstruction.
- Hierarchical scopes, ASSUME/PROVE, SUFFICES, CASE, QED and local definitions.
- TAKE, WITNESS, PICK, HAVE, USE/HIDE, INSTANCE and subexpression references.
- Arithmetic, sets, functions, choice and temporal backend proof reconstruction.
- Unchanged reference-proved corpus, false/circular/omitted-proof rejection,
  standalone imports and checked exported certificates.

Current hypothesis: compile SANY's resolved proof tree into Lean proof structure,
then normalize leaf obligations and reconstruct with kernel-producing tactics.
Competing paths for difficult leaves: direct reconstruction of backend proof
certificates; verified decision procedures. External solver success alone is
never evidence of a Lean proof. Source assertions must not become axioms.

Initial implementation: explicit leaf proofs generate Lean theorem declarations
and a certificate. Structured proofs are rejected pending implementation.
Verification is pending; the full proof port remains incomplete.

Leaf checkpoint: 4bef4fb, CI run 42048996808 passed. Five leaf theorem
statements produce a checked certificate; false leaves fail without replacing
existing output. Local suite: 46 tests plus prior native/source proof checks.
Hierarchical reconstruction now emits explicit Lean assertions and binder steps;
its kernel verification is pending. The reference source snapshot is pinned at
d1760ab9a1a3e7e76f81172166a955167cd163f2 in
/private/tmp/tlapm-proof-reference (task-owned, retained for corpus setup).

Hierarchical checkpoint: 73fc076, CI 42050998308 passed, including
TAKE/WITNESS/PICK/HAVE/CASE/SUFFICES and false intermediate-step rejection.
Scoped USE/HIDE DEF and standalone certificate imports are under verification.
USE facts are reconstructed as obligations. HIDE fact visibility, ONLY fact
selection, local definitions/instances, full backend reasoning and the full
reference corpus remain open; current success does not establish a full port.
