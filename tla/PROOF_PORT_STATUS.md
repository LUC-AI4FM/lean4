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

Continuation checkpoint (2026-11-05, function/choice reconstruction):
- Main CI 42064015546 passed symbolic arithmetic, module USE obligations,
  instantiation positives, and all 34 unchanged negative soundness fixtures.
- The behavior-substitution fix initially regressed four large source imports.
  793f894 factors instantiated bodies before free-behavior substitution, keeping
  bound state coordinates independent. The complete 433-module source audit
  42066760092 passed after this fix.
- ae9ee41 adds checked function graph/range/extensionality/update lemmas and
  eight unchanged upstream function proof fixtures. CI 42064844773 passed
  seven; excapp4_test exhausted proof search on a nested EXCEPT update.
- 020b0d0 adds apply_mem to forward proof search, checked CHOOSE case analysis,
  two unchanged choice fixtures, and a false-choice regression. The tactic
  derives a proved choice disjunction; it does not assume a witness exists.
  A normalization-resistant marker prevents repeating the same choice split.
- The 19 local frontend/proof-generation unit tests passed. Lean CI
  42069870841 is running for 020b0d0; these latest changes are NOT yet verified
  by the complete Lean suite. Earlier full proof audit coverage remains the
  baseline until a new all-input run completes. Full port remains incomplete.

Continuation checkpoint (2026-11-05, scoped proof steps):
- CI 42069870841 at 020b0d0 passed function/choice reconstruction, including
  nested EXCEPT, both unchanged CHOOSE fixtures, and all negative regressions.
- CI 42070566713 at c93a890 passed scoped CASE references and its false-case
  regression. CASE names denote the condition inside the case and the proved
  implication outside it. Later 8eddb22 also maps original quantified UIDs
  through TAKE; Cantor4 and EWD840 now translate past their unbound-variable
  errors. This later change is still awaiting its Lean suite.
- CI 42071298844 at e6955ce passed tuple indexing/domain/equality, string
  injectivity/membership, and record-domain fixtures. Record lookup was added
  afterward at f2c686f; revalidate run 42073507972.
- Proof audit 42070636502 at c93a890 is still running. Shards 0 and 1 each
  accounted for 95/95 inputs: shard 0 has 27/49 reference positives checked;
  shard 1 has 24/46 checked. Neither accepted a negative. Do not extrapolate
  these partial results to the full 379 inputs or 200 reference positives.
  Local artifacts: /private/tmp/tlaps-proof-audit-42070636502/shard{0,1}.
- 8eddb22 adds checked separation-subset and nonnegative-Int-to-Nat witness
  rules. 5d3c985 discharges bounded WITNESS membership immediately and keeps
  original witness bindings available to later CASE statements; the unchanged
  Cantor1 proof is now a positive regression awaiting Lean validation.
- 2af49aa fixes HAVE to match TLAPM's implication-premise introduction rather
  than an ordinary assertion, using an explicitly checked implication bridge.
  Invalid HAVE on a non-implication is rejected. Its unchanged upstream
  lsp/test/test_proof_steps.tla fixture awaits Lean validation. All 21 local
  frontend/proof-generation tests pass.
- Full proof port remains incomplete. Imported proofless induction libraries,
  temporal proof reconstruction, scoped ONLY/HIDE facts, remaining syntax and
  backend coverage, and proof-search limits still require work. No imported
  theorem may be assumed merely because TLAPS accepts its library declaration.

Audit 42070636502 is now terminal: shards 2 and 3 hit the job time limit.
All four checkpoint artifacts were retained, covering 349/379 inputs:
112 checked, 74 translation-rejected, 71 Lean-rejected, 56 per-file timeouts,
36 no-claims. Among 180/200 covered reference positives: 101 checked,
36 Lean-rejected, 32 timeouts, 11 translation-rejected. No false acceptance
was observed among covered inputs; 30 inputs remain unaccounted for in this
run. The next audit uses eight shards and a 45-minute job limit while keeping
the same per-file limit, to account for every input without dropping cases.

Eight-shard audit 42075998558 at 8efbef1 completed all 379/379 inputs.
Results: 129 checked, 80 translation-rejected, 72 timed out, 62 Lean-rejected,
36 no-claims. All 200 reference positives are accounted for: 118 checked,
37 timed out, 35 Lean-rejected, 10 translation-rejected. All 34 negatives
remain unproved: 19 timeouts, 13 Lean rejections, two translation rejections.
No false acceptance occurred. Outcomes and provenance are committed in
tests/proofs/lean-baseline.json. Later induction, generalized state facts,
simplifier, diagonal-set, Cartesian-product, and record-type changes are not
covered by this baseline and still require full Lean validation.

Continuation checkpoint (2026-11-05, reconstruction feedback):
- Focused CI 42081705655 at 9413571 passed natural and temporal induction,
  quantified CASE references, nested function updates, function extensionality,
  Cartesian products, and rejection of missing-base/temporal-scope regressions.
- Focused CI 42082565047 at 58a1356 additionally passed the unchanged Cantor1
  proof. Its only selected failure was the 30-field record: Aesop reached its
  default rule-application depth of 30. 16baf51 raises that depth to 128 while
  preserving existing time limits. Focused run 42083675025 is pending.
- Focused CI 42083147758 at 98beb36 passed an imported proofless true theorem
  and rejected an imported proofless false theorem. Imported declarations are
  independently reconstructed before being exposed as prior facts. Root
  missing proofs and explicit OMITTED proofs remain errors.
- Natural-induction search initially caused unrelated function-proof timeouts.
  34b1b44 gates it on the actual quantifier over TLA naturals; focused CI
  confirmed function proofs recovered. Temporal induction is likewise gated
  on a future-time quantifier and requires both base and successor proofs.
- Full eight-shard audit 42083872494 is running at 16baf51. Revalidate it and
  require all 379 inputs before comparing against tests/proofs/lean-baseline.json.
- Current local checks: all 23 frontend/proof-generation tests pass. A separate
  translation sweep covered all 60 then-existing positive fixtures. These are
  not substitutes for the Lean and full-corpus gates. Full port is incomplete.

Boolean and record checkpoint (2026-11-05):
- Focused run 42083675025 at 16baf51 passed the 30-field record, imported
  declaration, Cantor1 and temporal-induction proofs and selected negative tests.
- 7e6f33d adds a checked symmetric Boolean disequality rule. Focused run
  42085341479 passed unchanged Peterson MutexQ, the record and temporal tests,
  and rejection of FalseLeaf and FalseTemporalInduction.
- 4a4a41d adds separation-membership normalization plus unchanged Cantor2 and
  Cantor4 fixtures. Its focused run 42085864998 is pending; 23 local frontend
  tests pass. This is a candidate repair, not verified Cantor coverage.
- Full 379-input run 42083872494 at 16baf51 remains in progress. Completed
  shard 0 accounts for 48 inputs (20 checked, 11 Lean-rejected, 9 translation-
  rejected, 4 timeout, 4 no claims). It retains failures in Cantor variants,
  record equality and large temporal proofs. No complete aggregate yet.
- Full TLAPS compatibility remains incomplete. Continue from current diagnostics
  and keep positive/negative gates; do not treat focused passes as full coverage.

Record-domain and diagonal checkpoint (2026-11-05):
- 53a2c24 adds record_eq_keys, proved by domain congruence. Focused run
  42086388613 passed unchanged recordeq_difffields_smt_test, the 30-field
  record proof and false-leaf rejection.
- Separation normalization alone did not fix Cantor2/Cantor4 (42085864998).
  9e2d1dc applies the checked diagonal lemma before general search. Focused
  run 42086552560 passed both unchanged Cantor proofs, record-domain
  disequality, and FalseCaseReferences rejection. Local frontend tests: 23 pass.
- Partial full-audit artifacts from 42083872494: shards 0, 1, 3, 4 account for
  190 inputs. Of 96 reference-positive candidates encountered, 69 checked,
  18 timed out, 8 were Lean-rejected and one translation-rejected. All 16
  encountered negative inputs rejected or timed out. These are partial counts,
  not the final 379-input aggregate, and predate the newest fixes.
- Outstanding work includes full record extensionality, larger temporal proofs,
  exact fact visibility and remaining source/frontend compatibility. Keep the
  goal active; focused passing examples do not establish completion.

Finite record equality checkpoint (2026-11-05):
- 898dde5 proves record_as_pairs for records with unique field values per key,
  enumerate_eq_iff, and record_eq_iff. The backend compares concrete records
  through their finite pair sets, preserving field-order independence.
- Focused run 42087824037 passed unchanged recordeq_three_smt_test,
  recordeq_difffields_smt_test, the 30-field record test and false-leaf rejection.
- 49ba97d adds reordered-field equality and fieldwise equivalence tests, plus
  a false swapped-value equality. Focused run 42088157809 passed the positives
  and rejected the negative. These fixtures are also included in main CI.
- Local frontend suite: 23 tests passed. Main CI and the final shard of full
  audit 42083872494 remain pending. Seven completed shards cover 331 inputs:
  119/173 encountered reference positives checked, 39 timed out, 13 Lean-
  rejected, two translation-rejected. All 30 encountered negatives rejected
  or timed out. Do not substitute these partial counts for the full audit.
- Full port remains incomplete; continue remaining backend and frontend scope.

Complete audit checkpoint (2026-11-05):
- Run 42083872494 at 16baf51 accounts for all 379 inputs: 144 checked,
  86 timed out, 72 translation-rejected, 41 Lean-rejected, 36 without claims.
  Of the 200 reference-positive candidates: 132 checked, 50 timed out,
  14 Lean-rejected, four translation-rejected. All 34 negatives rejected
  or timed out; none accepted. tests/proofs/lean-baseline.json retains outcomes.
- Relative to the preceding complete audit, critical_bounded_test, excapp1_test
  and typingremainder_test regressed from checked to timeout. Retain and retest
  them; do not count aggregate gains as proof of no regression.
- Main CI 42083676762 at 16baf51 passed all its gates.
- beeec9a fixes descendant-process cleanup after prover timeouts; 25 local
  tests pass, including a spawned-child cleanup regression. Focused CI
  42089145550 is pending. f5bd06f adds a kernel proof of universal-set
  contradiction and unchanged Cantor3/Cantor10 fixtures (42089288668 pending).
- Full compatibility remains incomplete. The new full audit predates recent
  Boolean, Cantor, record equality and process cleanup repairs.

Cantor and timeout-regression verification (2026-11-05):
- Focused 42089145550 passed with process-group timeout cleanup, including
  record/Cantor proofs and false-record/temporal rejection.
- Focused 42089288668 at f5bd06f passed unchanged Cantor3 and Cantor10,
  plus false-leaf and false-record rejection. universal_set_contradiction
  is proved from foundation, not assumed.
- Focused 42089462628 passed all three prior timeout regressions:
  critical_bounded_test, excapp1_test and typingremainder_test, plus false-leaf
  rejection. This establishes current focused behavior, not corpus stability.
- Focused 42089746734 at bd5209f passed unchanged Cantor8, Cantor9 and
  Cantor10 plus false-leaf rejection. powerset_subset_contradiction is a
  proved inference connecting powerset inclusion, subset and nonmembership.
- Local tests: 25 pass. A new full compatibility audit was dispatched at
  bd5209f to measure all recent changes together. Full port remains incomplete.

Arithmetic and update-normalization checkpoint (2026-11-05):
- 4154d1b proves integer/natural exponent conversion and integer power typing.
  Initial focused 42090687981 compiled the backend but typingexp_test exhausted
  proof search; remainder and false-arithmetic checks passed.
- 8d96cdb adds conditional normalization for nonnegative integer exponents.
  Focused 42091220933 passed unchanged typingexp_test and rejected false
  arithmetic. That run still failed record_except_explosion_test.
- f16c031 adds checked unaffected updatePath projections and registers pre-order
  projection simplification. Focused 42090885988 passed ordinary EXCEPT and
  record equality plus false-record rejection, but the wide-record stress test
  still exceeded the simplification step limit.
- 8f848ff moves update/record domain simplification before value expansion.
  Focused 42091840982 is pending. Do not claim the wide-record failure fixed.
- Full audit 42090517540 at bd5209f remains active. Local 25-test suite passed
  before the final simplifier registration changes. Full port remains incomplete.

Wide-record proof checkpoint (2026-11-05):
- 168d33c tries bounded complete semantic simplification before the restricted
  normalization/search path. It only keeps the result when the proof closes;
  otherwise tactic backtracking preserves the existing path.
- Focused 42092855099 passed unchanged record_except_explosion_test,
  Cantor8 and typingexp_test, plus false CASE/temporal rejection. Local tests:
  25 pass. This resolves the selected wide-record failure in a focused run.
- Earlier 42091840982 timed out in SANY for every selected source before Lean
  ran. Its negative result is not evidence of backend rejection. 5c8ac96
  requires successful parser preflight for negative focused tests; parser
  failure now fails the check. Focused 42093328740 is pending.
- Full audit 42090517540 remains active. Five retained shards cover 237
  inputs: 100/124 encountered reference positives checked; 16 timeout,
  six Lean-rejected and two translation-rejected. No encountered negative
  accepted. Wait for all 379 inputs before replacing the complete baseline.
- Full TLAPS compatibility remains incomplete.

Full audit and broader reconstruction checkpoint (2026-11-05):
- Complete run 42090517540 at bd5209f accounts for 379/379 inputs: 164 checked,
  72 translation-rejected, 55 timeout, 52 Lean-rejected, 36 no claims.
  Reference positives: 152/200 checked, 32 timeout, 12 Lean-rejected, four
  translation-rejected. No previously checked reference positive regressed.
  All 34 negatives rejected or timed out (22 Lean, 10 timeout, two translation).
  The complete per-input baseline is retained in tests/proofs/lean-baseline.json.
- 42093328740 passed the wide-record and exponent proofs and false-record
  rejection with successful parser preflight. Earlier parser timeouts are
  not backend evidence.
- fbcc625 adds the existing checked range-extension theorem to proof search;
  unchanged broadcast decomposition is in focused run 42093846339 (pending).
  54ab1a9 adds nested/assumed/unequal record fixtures; run 42093974037 pending.
- 0cc2535 adds an explicit 1–600 second focused positive timeout, preserving
  the 15-second negative limit and 60-second full-audit baseline. The unchanged
  21-claim Enabled_test is being checked with 300 seconds in 42094215586.
  This is a separate experiment, not a reclassification of audit timeouts.
- Local 25-test suite passed before the workflow-only timeout changes.
  Full port remains incomplete; backend, frontend and visibility work remains.

Function/record reconstruction follow-up (2026-11-05):
- fbcc625 referenced ZFSet.is_func_extend_range, which is absent from this
  backend (the inspected external ZFLean source was not an imported API).
  769e0a3 replaces it with locally proved function_range_mono. Runs at older
  revisions, including 42094215586, cannot establish timing behavior because
  generated proofs reference the missing constant.
- 1ff6a0e proves record_eta from function extensionality and checked lookups.
  fb6fe0f adds enumerate_nil. Their backend builds passed, but focused
  42094940308 still failed broadcast, rectset and nested/assumed record proofs.
  FalseLeaf rejected after parser preflight. No claim that these cases work yet.
- Broad backward range widening caused excessive search; f7e5653 switches to
  forward inference requiring known function typing and containment facts.
  Focused 42095721026 checks range positives/negatives, ordinary EXCEPT and
  rectset. 42095109080 at the preceding revision is also still pending.
- 9d23413 adds explicit FunctionRange and FalseFunctionRange regressions to
  main CI. Local 25-test suite passed before the final rule-registration edit.
- Full port remains incomplete. Next: inspect these runs, diagnose rectset and
  record simplification, then resume remaining frontend/temporal coverage.
