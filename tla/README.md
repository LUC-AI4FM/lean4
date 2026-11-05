# TLA+ in Lean 4

Import existing `.tla` specifications or write specifications directly in Lean.
The source importer uses SANY for parsing, binding and level checking, then emits
Lean definitions over a common set-theoretic value universe. Lean checks proofs
about those definitions. The full port is still in progress; the
[acceptance record](PORT_STATUS.md) tracks verification and remaining work.

## Import a specification

Install Lean's `elan`, Java 11 or later, and Python 3.11 or later. From `tla/`:

```sh
python3 tools.py
cd universal
lake update
lake exe cache get
python3 ../translate.py ../tests/Counter.tla -o Counter.lean
lake env lean Counter.lean
python3 check.py
```

Use `-I directory` to resolve additional source modules. Input files remain
unchanged. Output is written after successful translation. Generated modules
expose their constants and operators; an operator takes its parameters, constants,
a behavior and a time index. Source operator parameters become Lean expressions,
so priming retains their state dependence.

`tools.py` verifies the official TLA+ 1.7.4 tool archive by SHA-256. The package
pins Lean 4.33.0 and ZFLean, which pins Mathlib. The dependency cache avoids
rebuilding Mathlib. No upstream Lean compiler build is required.

## Native specifications

The universal API is the same API used by source imports:

```lean
module
import TLAUniversal
open TLAUniversal
noncomputable section

def Init : Expression := liftPredicate (fun s => s "x" = integer 0)
def Next : Expression := liftAction
  (fun s t => t "x" = intBinary (· + ·) (s "x") (integer 1))
```

Values are ZFC sets. Integers, booleans, strings, mixed collections, functions,
records and sequences share this universe. Functions use ordered-pair graphs;
records and sequences use string and integer domains, respectively. Native APIs
include set operations, choice, function updates and recursive fixing graphs.

`TLA.Basic` provides predicates, actions, infinite behaviors, always/eventually,
leads-to, ENABLED, stuttering frames, fairness, composition and temporal hiding.
It includes invariant induction and fairness proofs. The separate typed `TLA`
package provides an ergonomic API for typed native specifications without
Mathlib. Run its checks from `tla/` with `python3 check.py`; select the narrower
source backend explicitly with `translate.py --backend typed`.

## Checked proofs

`universal/CounterProof.txt` proves the unchanged counter source specification's
invariant, including stuttering. Append it to the generated counter module to
check the proof. `tests/Native.lean`, `tests/Data.lean` and `tests/Temporal.lean`
exercise the typed native APIs. Both CI jobs reject deliberately false proofs.

Source `ASSUME` and `THEOREM` statements become explicit assumptions and claims.
A generated `Certificate` requires Lean proofs of the claims. Structured
`ASSUME NEW ... PROVE ...` obligations retain their quantifiers. Source proof
hints, including `OBVIOUS` and TLAPS pragmas, do not supply trusted proofs.

## Source coverage

The importer supports resolved module substitutions, LET, operator parameters,
integer arithmetic, conditionals, CASE, mixed sets and tuples, bounded/unbounded
quantification and choice, tuple binders, Cartesian products, functions, records,
nested EXCEPT, sequences, finite sets and cardinality. Temporal support includes
priming, UNCHANGED, action frames, ENABLED, composition, always/eventually,
leads-to, fairness and flexible quantification.

Recursive functions use choice of a fixed-point graph. Recursive operators use
the fixing-graph semantics described by
[Gonthier and Lamport](https://lamport.azurewebsites.net/pubs/recursive-ops.pdf).
Mutually recursive value operators share one tagged fixing graph. Defining
equations are not introduced as axioms; unfolding needs a proof.

Tests include unchanged, pinned TLA+ project examples: DieHard, CoffeeCan,
DiningPhilosophers and Bakery. Provenance and licenses are in `tests/corpus`.
TLC differential tests also check record and sequential EXCEPT behavior.

## Remaining work

Higher-order recursive operators, real arithmetic, the complete
standard-module library, some level-specific `NEW` declarations, and source
proof-script translation remain incomplete. Unsupported constructs fail with a
diagnostic. There are no added axioms or placeholder proofs.

The concrete value representation chooses values for operations outside their
specified domains. A proof about that representation is not automatically a
source-language theorem: general source correspondence and definedness proofs
remain open. The compiler is currently part of the trusted translation path.
This port does not yet replace TLC or TLAPS.

The upstream Lean compiler and kernel are unchanged. The implementation lives
in `tla/` and builds independently.
