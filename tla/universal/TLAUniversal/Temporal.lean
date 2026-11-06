/- Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license. -/
module
public import TLA.Basic

/-!
Propositional temporal rules used by `BY PTL` leaves.

Every rule is an ordinary Lean theorem over time-indexed predicates
`Nat → Prop` (atoms abstracted from the behavior). The proof tactic only
selects rules and instantiates their atoms; the kernel checks each use.
-/

@[expose] public section
namespace TLAUniversal.PTL

/-- Persistence: a predicate preserved by every step from time `j` holds
from `j` onwards. -/
theorem persist (p : Nat → Prop) (j : Nat) (start : p j)
    (step : ∀ k, j ≤ k → p k → p (k + 1)) : ∀ k, j ≤ k → p k := by
  intro k hk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction d with
  | zero => simpa using start
  | succ d ih => exact step (j + d) (by omega) ih

/-- Weak fairness, stated over abstract enabledness and step atoms: if the
action is continuously enabled from some time on, it is taken infinitely
often. `TLA.weakFairness` unfolds to this shape. -/
def Fair (n : Nat) (en step : Nat → Prop) : Prop :=
  (∃ k, n ≤ k ∧ ∀ m, k ≤ m → en m) → ∀ m, n ≤ m → ∃ j, m ≤ j ∧ step j

theorem weakFairness_fair {σ α} (a : TLA.Action σ) (v : σ → α) (b : TLA.Behavior σ) (n : Nat)
    (h : TLA.weakFairness a v b n) :
    Fair n (fun k => TLA.enabled (TLA.angle a v) (b k))
      (fun k => TLA.angle a v (b k) (b (k + 1))) := h

theorem strongFairness_fair {σ α} (a : TLA.Action σ) (v : σ → α) (b : TLA.Behavior σ) (n : Nat)
    (h : TLA.strongFairness a v b n) :
    Fair n (fun k => TLA.enabled (TLA.angle a v) (b k))
      (fun k => TLA.angle a v (b k) (b (k + 1))) :=
  TLA.strong_implies_weak a v b n h

/-- The WF1 rule with one persistent rank, proved by contradiction.

Assume `Q` never holds from time `t ≥ n` on. Then the action is enabled
throughout, so fairness yields infinitely many steps. A step from a state
with `P` contradicts `done`; a step from `¬P` establishes `P`, which then
persists until the next step. With `P := fun _ => True` this is the plain
WF1 rule `P ∧ <<A>> ⇒ Q'`. -/
theorem wf_rank (en step P Q : Nat → Prop) (n t : Nat) (fair : Fair n en step) (ht : n ≤ t)
    (enabled : ∀ k, t ≤ k → ¬ Q k → en k)
    (persists : ∀ k, t ≤ k → ¬ Q k → ¬ Q (k + 1) → P k → P (k + 1))
    (done : ∀ k, t ≤ k → ¬ Q k → ¬ Q (k + 1) → P k → step k → False)
    (advance : ∀ k, t ≤ k → ¬ Q k → ¬ Q (k + 1) → ¬ P k → step k → P (k + 1)) :
    ∃ k, n ≤ k ∧ Q k := by
  classical
  apply Classical.byContradiction
  intro absent
  have never : ∀ k, t ≤ k → ¬ Q k := fun k hk hq => absent ⟨k, Nat.le_trans ht hk, hq⟩
  have steps := fair ⟨t, ht, fun m hm => enabled m hm (never m hm)⟩
  obtain ⟨j, hj, sj⟩ := steps t ht
  have pj : P (j + 1) := by
    by_cases hp : P j
    · exact (done j hj (never j hj) (never (j + 1) (by omega)) hp sj).elim
    · exact advance j hj (never j hj) (never (j + 1) (by omega)) hp sj
  have always := persist P (j + 1) pj fun k hk hp =>
    persists k (by omega) (never k (by omega)) (never (k + 1) (by omega)) hp
  obtain ⟨i, hi, si⟩ := steps (j + 1) (by omega)
  exact done i (by omega) (never i (by omega)) (never (i + 1) (by omega)) (always i hi) si

/-- Eventualities can be used from the time they occur. -/
theorem eventually_from (R Q : Nat → Prop) (n : Nat) (h : ∃ k, n ≤ k ∧ R k)
    (rest : ∀ t, n ≤ t → R t → ∃ k, t ≤ k ∧ Q k) : ∃ k, n ≤ k ∧ Q k := by
  obtain ⟨t, ht, r⟩ := h
  obtain ⟨k, hk, q⟩ := rest t ht r
  exact ⟨k, Nat.le_trans ht hk, q⟩

end TLAUniversal.PTL
