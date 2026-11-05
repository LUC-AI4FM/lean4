# TLA+ in Lean 4

An initial port with two entry points: write specifications directly in Lean or
translate an existing `.tla` file into Lean. Both use `TLA.Basic`, and proofs are
checked by the Lean kernel. This is an experimental integer/action fragment,
not a complete TLA+ implementation or a replacement for TLC/TLAPS.

## Run

Install Lean's `elan` toolchain manager, then run from this directory:

```sh
python3 check.py
python3 translate.py tests/Counter.tla -o Counter.lean
lake env lean Counter.lean
```

The package pins Lean 4.33.1 and has no third-party Lean or Python dependencies.
It can be checked independently of a full build of the forked Lean compiler.
`check.py` builds the library, tests translation and rejection cases, checks
native and translated invariant proofs, and verifies that a false proof fails.

## Native specifications

```lean
module
import TLA

def Init : TLA.Predicate Int := fun x => x = 0
def Next : TLA.Action Int := fun x y => y = x + 1
def Spec : TLA.Formula Int := TLA.spec Init Next
```

See `tests/Native.lean` for a complete invariant proof and stuttering/fairness
examples. Native specifications may use any Lean state type. The library provides
state predicates, actions, infinite behaviors, always, eventually, leads-to,
ENABLED, UNCHANGED, square/angle actions, and weak/strong fairness. `TLA.invariant`
proves safety for every infinite behavior satisfying Init and the stuttering
closure of Next. No axioms or `sorry` declarations are added by this package.

Semantics follow the action/behavior definitions in
[Specifying Systems](https://lamport.azurewebsites.net/tla/book.html).
Fairness uses enabled **non-stuttering** actions relative to the supplied frame.

## Existing `.tla` source

`tests/Counter.tla` is an ordinary, unchanged TLA+ module:

```tla
---- MODULE Counter ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x + 1
Inv == x >= 0
Spec == Init /\ [][Next]_x
====
```

The translator emits a Lean `State` structure and definitions. Append the proof
in `tests/CounterProof.txt` to the generated module to prove its invariant.
Translation does not prove any property automatically.

Current source subset:

- One module; `EXTENDS Integers, Naturals`; integer-valued variables.
- Zero-argument state predicate and action definitions, in dependency order.
- Integer literals, primed variables, parentheses, unary minus, `+`, `-`, `*`.
- Integer comparisons, TRUE/FALSE, conjunction, disjunction, implication,
  equivalence, and negation of parenthesized predicates.
- References to earlier state predicates, and `UNCHANGED variable`.
- `Init /\ [][Next]_vars`, with a scalar or tuple containing all variables in
  declaration order.
- Line comments and nested block comments.

All source variables have domain `Int` in this first fragment. `Naturals` does
not implicitly constrain them to nonnegative values; use an invariant/init
condition. Source definitions must return a proposition. Actions and temporal
formulas cannot yet be referenced inside arbitrary expressions.

Unsupported syntax raises a diagnostic before writing output. In particular,
sets, membership, records, sequences, function values, quantifiers, constants,
operator parameters, IF/THEN/ELSE, LET, CHOOSE, INSTANCE, recursive definitions,
PlusCal, proof syntax, and general temporal source expressions are not ported.
Use explicit parentheses for logical grouping. The Python translator is part
of the trusted source-to-Lean translation path: Lean checks the generated
statement and its proof, not a proved correspondence with the original text.

## Remaining port work

1. Define a value universe and set/function semantics for untyped TLA+.
2. Add a source AST, level checking, module resolution and standard modules.
3. Extend source translation to general temporal formulas and operator binding.
4. Validate source semantics against the reference tools and prove translation
   correspondence for the supported fragment.
5. Add proof-language interoperability and broader upstream compatibility tests.

The upstream compiler and its kernel are unchanged. The package is kept in
`tla/` so upstream Lean changes can be incorporated without a compiler patch.
