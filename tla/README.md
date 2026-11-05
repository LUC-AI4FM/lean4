# TLA+ in Lean 4

Write specifications directly in Lean, or translate existing `.tla` modules to
Lean definitions. Both paths use the temporal and data semantics in `TLA`.
The full port is in progress; see [the acceptance record](PORT_STATUS.md).

## Run

Install Lean's `elan` toolchain manager, Java 11 or later, and Python 3.11 or
later. From this directory:

```sh
python3 tools.py
python3 check.py
python3 translate.py tests/Counter.tla -o Counter.lean
lake env lean Counter.lean
```

`tools.py` downloads the official TLA+ 1.7.4 tools and verifies a pinned SHA-256.
There are no third-party Python packages or Lean dependencies. The package pins
Lean 4.33.0 and builds independently of the upstream compiler in this fork.
Use `-I directory` for additional source-module search paths.

`check.py` builds the library, checks source parsing and compilation, verifies
native and translated proofs, and confirms that a false proof fails. Tests cover
invalid priming, module substitution, lexical binding, generic sets, TLC record/update comparisons, collection
semantics, stuttering, fairness and output preservation after failed translation.
CI downloads and verifies the same pinned reference tools before running tests.

## Native specifications

```lean
module
import TLA

def Init : TLA.Predicate Int := fun x => x = 0
def Next : TLA.Action Int := fun x y => y = x + 1
def Spec : TLA.Formula Int := TLA.spec Init Next
```

`tests/Native.lean` proves the counter invariant and checks stuttering/fairness.
`tests/Data.lean` proves collection and function-update properties. The native
library provides:

- State predicates, actions and infinite behaviors.
- Always, eventually, leads-to, ENABLED, UNCHANGED, square/angle actions.
- Weak/strong fairness, invariant induction, and strong-implies-weak fairness.
- Extensional sets, comprehensions, images, powersets, union and choice.
- Functions with explicit domains, extensionality, application and update.
- Typed sequences with one-based indexing and subsequences.

Semantics follow the action/behavior definitions in
[Specifying Systems](https://lamport.azurewebsites.net/tla/book.html).
Fairness uses enabled **non-stuttering** actions relative to the supplied frame.
Set/function proofs use Lean's classical logic; this library adds no axioms or
`sorry` declarations.

## Existing source

The CLI uses the official SANY parser and level checker, consumes resolved
symbol identities, and emits inspectable Lean code. It rejects parser/level
errors even when the reference exporter exits with status zero. Local files
cannot shadow trusted standard modules. Output is written only after translation
succeeds.

`tests/Counter.tla` and `tests/fixtures/Collections.tla` demonstrate unchanged
source input. The latter covers sets, quantifiers, functions, operator parameters,
LET, conditionals, action references and fairness. Local module `INSTANCE`
substitutions are expanded using resolved bindings rather than textual replacement.

Generated modules expose `Constants`, `State`, and definitions taking constants,
a behavior and a time index. Value types are inferred; unconstrained types remain
explicit generic Lean types. Append `tests/CounterProof.txt` to the translated
counter to check its invariant. Translation alone does not prove a property.

Supported source constructs currently include:

- Constants, variables, operator calls, LET and INSTANCE substitutions.
- Integers, arithmetic, comparisons, propositional operators and IF/THEN/ELSE.
- Set enumeration, intervals, membership, union/intersection/difference, subset,
  powerset, UNION, comprehensions, multiple bounded quantifiers and bounded CHOOSE.
- Function constructors, application, DOMAIN and function spaces.
- Records, record sets, nested EXCEPT, and sequential @ update semantics.
- Homogeneous tuples/sequences, Len, Append, Head, Tail, SubSeq and concatenation.
- Priming, UNCHANGED, action frames, ENABLED, always/eventually and fairness.

## Remaining compatibility boundaries

The generated data interpretation is currently **typed**. It is not yet a faithful
universal model of all untyped TLA+ values. Heterogeneous collections, mixed
function/record/sequence equality, unrestricted quantification and arbitrary
recursive definitions require further semantic work. Tuple binders and multi-argument function constructors, operator-valued parameters/constants, temporal hiding,
general standard modules, and proof/assumption obligations also remain incomplete.
Unsupported constructs are rejected, never replaced by axioms or placeholder
proofs. Source ASSUME and THEOREM declarations are currently rejected so they
cannot silently disappear from a translated module.

Some operations outside their specified mathematical domains have total Lean
values; source claims about such operations are not covered by a correspondence
theorem. The SANY-to-Lean compiler remains part of the trusted translation path.
Lean checks generated statements and proofs, not a proved equivalence to source.
This package is not yet a replacement for TLC or TLAPS.

The upstream Lean compiler and kernel are unchanged. The port lives in `tla/`
to allow upstream compiler updates without a kernel patch.
