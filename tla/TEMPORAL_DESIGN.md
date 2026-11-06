# Temporal proofs: PTL, fairness and ENABLED

Status: design, not implemented. Covers the corpus inputs that fail for
missing temporal reasoning (SimpleEventually, SimpleEventuallyInt,
SimpleExampleWF, FOLTL, EWD840 liveness, Euclid Correctness, the
enabled_cdot tests).

## What TLAPS does

`BY PTL` sends the obligation to a propositional temporal logic decision
procedure (LS4) after abstracting every non-temporal subformula to an
atom. Facts cited in the BY become hypotheses `[]F` or `F` as written.
ENABLED is expanded by `ExpandENABLED` / `ENABLEDrules` into an
existential over the primed variables, and `\cdot` into an existential
over an intermediate state.

## What the port has today

- Behaviors are `Nat → State`; `[]P` at `n` is `∀ k ≥ n, P k`;
  `<>P` is `∃ k ≥ n, P k`; WF/SF are defined in `TLA` and simp-unfolded.
- `tla_temporal_induction` proves `∀ k ≥ n, P k` by induction, which
  covers the safety pattern `Init /\ [][Next]_v => []Inv`.
- No liveness rule, no ENABLED witness construction.

## Design

1. **Atom abstraction, checked.** For a `BY PTL` leaf, collect maximal
   non-temporal subterms of the goal and cited facts as atoms `a_i : Nat → Prop`
   (each is a lambda over the time index). Generalize them in Lean
   (`generalize`), leaving a goal in a small temporal fragment over
   `Nat → Prop`. Soundness: generalization only weakens the goal.
2. **Decision procedure as a Lean tactic, not a trusted oracle.** Implement
   the PTL fragment used by the corpus (`[]`, `<>`, `~>`, WF/SF over
   atoms) as tactic rules that each produce a kernel-checked term:
   - safety induction (existing),
   - leads-to chaining: `P ~> Q`, `Q ~> R` ⊢ `P ~> R`,
   - WF rule: `[](P /\ [N]_v => P' \/ Q')`, `[](P /\ <<N /\ A>>_v => Q')`,
     `[](P => ENABLED <<A>>_v)` ⊢ `WF_v(A) => (P ~> Q)`,
   - SF analogue with `[]<>ENABLED`,
   - lattice/well-founded leads-to for counters (SimpleEventuallyInt).
   Each rule is a Lean theorem in `TLAUniversal`; the tactic only selects
   and applies them. An LS4-style search may propose the rule sequence; its
   answer is never trusted without the Lean term.
3. **ENABLED witnesses.** `ENABLED A` at state `s` is `∃ s', A(s, s')`.
   Build the witness state from A's syntactic shape: for conjuncts
   `x' = e` set `x ↦ e`, keep `UNCHANGED` variables, and leave others as
   `s x`. Emit `refine ⟨fun v => if v = "x" then e else ..., ?_⟩` and let
   the existing leaf search prove the action. `\cdot` gets the same
   construction for the intermediate state.
4. **Generalized priors.** Temporal steps need facts at every time; the
   existing `_general` step variants already provide `∀ b n` forms when
   no state hypothesis is in scope.

## Negative tests to add with the implementation

- WF on the wrong action, SF replaced by WF where SF is required,
  leads-to with a missing progress step, ENABLED of an action whose
  guard is false, and `[]<>` vs `<>[]` confusion. Each must be rejected.

## Library induction theorems (prerequisite for several inputs)

NaturalsInduction, WellFoundedInduction and SequenceTheorems statements
are imported as obligations and currently need Lean proofs of their
statements. Plan: prove NatInduction, DownwardNatInduction,
GeneralNatInduction and SmallestNatural once in `TLAUniversal` against
the universal-value encoding of `Nat`, then let the generated proof
discharge an imported claim by `exact` of the library lemma when its
statement matches, falling back to search otherwise. No statement is
assumed: an unmatched claim stays an obligation.
