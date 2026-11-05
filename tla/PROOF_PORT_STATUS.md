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

Verified checkpoints:
- c52cae0: complete main CI 42052439148 passed, including separate imports of
  generated proof certificates and scoped USE/HIDE DEF.
- e50d151: complete main CI 42052750103 passed, including ground arithmetic,
  finite-set membership and a false arithmetic proof rejection.
- Upstream unchanged proof audit 42052441125 is running on all 379 pinned
  TLAPM `.tla` files. It preserves per-file diagnostics and distinguishes
  modules without claims and intentionally false soundness inputs. It does
  not establish that all other files are reference-proved positive tests.
- 089b4d3 local DEFINE and level-specific NEW reconstruction, and e41e8cd
  simple SUFFICES / NEW VARIABLE reconstruction await final CI results.

Latest verified checkpoint: 3f595c9; complete main CI 42055963982 passed.
All 13 unchanged upstream syntax/proof fixtures and the imported TLAPS
foundation fixture now produce checked certificates and pass separate imports.
The false leaf, intermediate-step, arithmetic and omitted-proof regressions
still reject. 63d687d adds proved Boolean and nonuniversality lemmas, not axioms.

First full mixed audit (c52cae0, run 42052441125): 379/379 accounted for;
31 checked, 37 no claims, 171 Lean-rejected, 120 translation-rejected, 20
 timed out. None of the 34 expected-false soundness inputs was accepted.
Every per-file status is retained in tests/proofs/audit-baseline.json; full
artifacts are in /private/tmp/tlaps-proof-audit-42052441125 and on GitHub.
More than 90 Lean failures first hit the imported nonuniversality lemma, now
fixed. The audit predates local DEFINE, NEW binders and arithmetic support.
Second full audit is RUNNING: 42057016191 at 3f595c9, with pinned CommunityModules
available to resolve Functions and other library dependencies. Download its
four reports and compare before choosing the next implementation tranche.

Next gates: establish reference-proved positives (the mixed audit is not that
baseline); reconstruct theorem/CASE references with correct goal and temporal
scope; generalize prior proved facts beyond the current behavior/time; bounded
multi-WITNESS and tuple binders; scoped facts/ONLY/HIDE; arithmetic, set,
function and temporal backend coverage. Do not count omitted/invalid/parser-only
inputs as failed positive proofs or rejected negatives as checked backend tests.

Reference baseline discovery: official tlaplus/tlapm release 1.6.0-pre offers
Linux asset tlapm-1.6.0-pre-x86_64-linux-gnu.tar.gz, 51958583 bytes, SHA256
3357e45d1142346fb27dbcdbaee05ed4dcb0378cc99e0eb14636c762158aee8d
(observed 2026-11-05, rolling asset updated 13:22:58Z). Its --version reports
source commit. Use a pinned/checksummed offloaded workflow for reference runs;
do not run substantive prover workloads on the Mac. Baseline workflow has not
yet been implemented. Native goal remains active; the full port is incomplete.

Continuation checkpoint (2026-11-05):
- Strict TLAPS baseline 42057966135 completed: reference binary efe4f2d,
  213 reported proved, including 13 explicitly false known soundness tests.
  200 non-negative reference-proved candidates are recorded in
  tests/proofs/reference-baseline.json. False reference successes remain
  negative tests, not compatibility targets. Four reference inputs timed out.
- Second Lean audit 42057016191 at 3f595c9 completed all 379 inputs:
  90 checked, 134 Lean-rejected, 95 translation-rejected, 37 no claims,
  21 timed out, TWO false inputs accepted. Among the 200 reference positives:
  80 checked, 82 Lean-rejected, 20 translation-rejected, 17 timeouts, one
  module USE-only input with no generated claim.
- The two accepted false claims concern aliased module instantiation under
  strong fairness and guarantees (-+->). This revealed a compiler semantics
  defect, not a Lean kernel defect. 97f2f2d instantiates the free behavior
  before binding original state coordinates; it disables cached instantiated
  definitions inside that environment so substitution is not repeated.
- CI 42061752128 at 97f2f2d confirmed positive instantiation/ENABLED proofs,
  tuple binders, bounded witness annotations, and rejection of both false
  instantiation regressions. It failed only the symbolic remainder test:
  normalization changes the upper-bound goal to a strict inequality. The
  direct checked Int.emod_lt_of_pos rule is now being added.
- All 34 unchanged upstream soundness tests are in tests/proofs/negative;
  d8ac1df also checks module-level USE facts, including USE FALSE rejection.
- Current main CI 42062953878 at d8ac1df is running; the full 433-module
  specification audit 42063087821 is running after the behavior-instantiation
  fix. Revalidate both; the previous 433/433 result predates this change.
- Reference artifacts: /private/tmp/tlaps-reference-42057966135.
  Second audit artifacts: /private/tmp/tlaps-proof-audit-42057016191/full.
  GitHub had transient commit_refs_rules/HTTP 500 errors; ordinary retries
  succeeded, without force pushes or changing access policy.

Remaining scope is still the full proof port. In addition to backend coverage,
remaining issues include CASE-step references, temporal fact scopes, module
instantiation/level correctness beyond the captured regressions, and source
syntax accepted by TLAPM but rejected by the pinned SANY frontend. Do not mark
complete on the 200-case subset, on parser acceptance, or on theorem statements
whose source proof steps were not reconstructed and checked.
