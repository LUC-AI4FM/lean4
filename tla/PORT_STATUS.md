# TLA+ port acceptance record

## Verified delivery — 2026-11-05

Both interfaces are implemented: unchanged `.tla` source imports and Lean-native
specifications over the same semantics. The specification-port acceptance gates
below are covered by the following published checks:

- [Primary verification, 082c87a](https://github.com/LUC-AI4FM/lean4/actions/runs/41981536798):
  43 Python/reference tests, all 61 standard-module exports, native and imported
  proofs, separate-module consumers, and rejection of false proof certificates.
- [Full upstream corpus, 038dd0d](https://github.com/LUC-AI4FM/lean4/actions/runs/41981249939):
  433 distinct unchanged modules from the pinned tlaplus/Examples revision;
  all 433 passed source translation and Lean elaboration, with no skipped inputs.
  The translator is unchanged between this revision and 082c87a.
- The source/native counter equivalence and invariant proofs pass, as do
  higher-order recursion base cases and the general well-founded correctness
  theorem. No axioms or placeholder proofs were added to the implementation.

The source frontend remains the pinned official SANY implementation. The
translator is part of the trusted translation path. Source proof scripts supply
claims and assumptions; generated certificates require Lean proofs rather than
trusting TLAPS tactics. Tool-specific runtime side effects are not executed.
These boundaries are described in the README; corpus acceptance does not assert
that every imported specification or source theorem is correct.

## Implementation record

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

Initial frontier: official SANY semantic XML frontend versus expanding handwritten
syntax. SANY has native grammar/level/module resolution, so test that interface
first. Exporter limitations must produce explicit diagnostics, never placeholders.

Verification: bounded library/proof checks on the coordinator; sustained builds
and larger corpus work require an authorized LUC host or public GitHub CI.
No new paid resources. No delegated agents or persistent remote workloads.

Initial next step: pin reference tools; import and validate the SANY graph; replace textual
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


Record/update checkpoint: 20 tests and all native/source proof checks pass.
TLC differential testing caught and fixed sequential EXCEPT @ semantics.
Typed frontend b90197d CI passed. Record/EXCEPT changes now covered by both TLC
and Lean proofs. Universal-value branch uses pinned Apache-2.0 ZFLean commit
ae928234e7ed6b26241344ef4ba6d7cf98c0ed91 (Lean 4.33.0) in a separate Lake package;
its initial proofs are pending public CI, not claimed verified. Builds are kept
off the coordinator. Public dependency source reference is retained temporarily
at /private/tmp/lean4-tla-zflean-reference for API inspection.


Universal CI diagnosis: Lake promoted the child package from 4.33.0 to the parent
4.33.1, invalidating the pinned Mathlib cache. Aligned the parent package to 4.33.0
rather than rebuilding Mathlib on the coordinator. Existing local lightweight
checks may use installed 4.33.1 explicitly; CI checks the pinned 4.33.0 build.
Added multiple bounded quantifiers/comprehensions with generated Lean proofs.


Universal CI reached Lean and exposed two concrete failures: temporal aliases
were restricted to Type 0, and one domain proof destructuring pattern failed.
Generalized temporal definitions to universe-polymorphic state types and fixed
that proof. Added universal source generation and heterogeneous/quantifier/operator
fixtures; those are queued for CI, not yet claimed passing. Main typed lane passed.


Proof-obligation and temporal checkpoint: named ASSUME/THEOREM graph references
retain their formula bodies; generated Certificate structures require real Lean
proofs, and a false certificate is rejected. Added action composition and
stuttering-aware flexible quantification to the universe-polymorphic native core.
Universal source renderer now includes temporal hiding and leads-to. Universal
CI found only an over-expanding simp invocation in integer arithmetic's bridge
lemma; replaced it with explicit guarded rewriting. Universal source tests still
await a full passing run. All previous limitations remain until their gates pass.

The universal lane passed at 1718e9a (GitHub run 41964157439), including
mixed collections, records, temporal hiding, tuple binders, products and CASE.
The next gate adds a source Counter invariant proof and parameterized native
exports. Control-character strings now use a lossless SANY adapter when the
official XML 1.0 serializer fails; source files remain unchanged.

Run 41964655689 passed at 5aec0b8: the universal Counter source invariant is
kernel-checked, parameterized operators are exported, and control strings pass
both frontend and Lean checks. Recursive operator implementation now follows
Gonthier–Lamport's fixing-graph semantics (recursive-ops.pdf section 3.1), not an
unconditional fixed-point equation. Recursive function definitions use CHOOSE.
Higher-order and mutually recursive operators remain open coverage gates.

Run 41965032146 passed at 8a8d3df, including finite-set/cardinality definitions,
recursive source modules and the kernel-checked fixing-graph witness/constant
lemmas. The corpus now includes unchanged MIT-licensed tlaplus/Examples modules
at 0e32a039a4286cc3e1b0f70c00eaff3178d49f85: DieHard, CoffeeCan,
DiningPhilosophers and Bakery. Their source provenance and licenses are retained.
Bakery's TLAPS pragma dependency is pinned separately with its BSD license;
pragma hints do not discharge generated Lean obligations.

Run 41966351016 passed at 0f47e67: shared operator output avoids Bakery's
elaboration timeout, all four upstream corpus modules elaborate, structured
proof certificates check, mutual recursion imports, and the common rational-cut
numeric encoding has checked injectivity and decoding proofs. Integration of
that encoding into real/integer arithmetic is in the next CI gate. The source
CLI now defaults to universal values; the typed backend is an explicit option.

The builtin operator audit added `-+->` using finite-prefix extendability and the
one-state-longer condition from Specifying Systems §16.2.4. Native guarantees
proofs pass locally. Source labels/subexpressions, LAMBDA, forwarded operator
arguments and STRING universes are now covered by fixtures. The pinned SANY
frontend rejects operator-valued recursive parameters; they are not silently
accepted by the importer.

Run 41968420324 passed at 4cbb7ca: shared integer/real arithmetic and the source
real-number proofs pass, as do recursion, standard-library fixtures, level-aware
claims and the original corpus. Added unchanged Consensus, Paxos, Voting,
TwoPhase, Alternate, Majority and Prisoners modules, with pinned TLAPS theorem
and CommunityModules dependencies. The expanded corpus is awaiting CI; imported
library theorem statements remain obligations, not trusted source proofs.

Run 41969344493 passed at 49b18fc: all eleven unchanged upstream example
modules elaborate, as do real-time, TLC mathematical library, name collision,
module-instantiated theorem, and level-specific claim fixtures. Added universal
collection lemmas and source proof tests; their verification is pending. TLC
rejects cross-type equality when testing membership in a mixed set, so that
case remains a Lean-only proof test; tuple and function reads are differential
checks within TLC's supported domain.

Run 41969868406 passed at b065c93: mixed-set membership, heterogeneous tuple
indexing and function application are proved from generated source definitions.
Local reference checks now include tuple/function positive and negative cases.
The LOCAL INSTANCE audit exposed copied declaration locations in standard
libraries; source-body provenance now resolves them, with Randomization and
Toolbox fixtures queued. A source THEOREM FALSE / OBVIOUS certificate regression
adds a direct check that source proof hints cannot manufacture a Lean proof.

The broader library audit added all exported bag and sequence operations,
Randomization and Toolbox. It found and fixed an unconstrained Lean universe
in boolean-only equality. Separate-file verification also caught generated
private declarations; both backends now export public, exposed definitions and
compile a consumer proof file. The typed consumer check passes locally. Universal
sequence length, source hiding/guarantees, and nested parameterized INSTANCE
proofs are in the current CI gate. Local suite: 33 tests plus native and typed
source/consumer proofs pass. Full compatibility is not claimed by these results.

Run 41971199364 passed at 75a02c0, including separate-module universal proofs,
sequence length, nested module instances, stuttering-aware source proofs, all
eleven upstream modules and source false-certificate rejection. Run 41971950715
passed at 6c0c6d7 with all 61 exported standard operators covered by reachable
fixture calls and 34 Python/reference tests.

The deeper numeric audit against Specifying Systems §18.4 found that the numeric
modules share real arithmetic even without EXTENDS Reals. The universal backend
now follows that rule, supports real/negative exponents, real interval endpoints
and both infinities. Run 41972377311 checked these definitions and all fixtures
except one proof normalization step for negative exponentiation, since corrected.
Additional CHOOSE-defined zero-division and bounded-quantifier proof checks are
in flight. General source correspondence remains an explicit trust boundary.

Runs 41973033334, 41973843482 and 41974760552 passed the numeric/binder,
nested-call and generated-namespace regression gates. The first complete audit
of all 433 pinned tlaplus/Examples modules (41974274420) passed 374 and retained
every failure in per-shard JSON artifacts. Failures exposed warning-only SANY
handling, operator-valued builtin arguments, parameterized theorem metadata,
custom standard-module names, name capture, missing support modules and code
expansion limits. Run 41977084643 passed the fixes and their proof regressions.

The larger corpus exposed two additional cases: concatenated top-level modules
in BufferedRandomAccessFile.tla and repeated expansion of closed module-local
standard-library definitions. The importer now resolves the bundled modules in
a temporary directory without editing the input; shared closed definitions and
dependency-ordered INSTANCE exports reduce generated code size. Local checks:
41 Python/reference tests, all 61 standard exports, native/source proofs and
false-proof rejection pass. Universal and full-corpus verification of these
latest changes is running; full compatibility remains unclaimed.
