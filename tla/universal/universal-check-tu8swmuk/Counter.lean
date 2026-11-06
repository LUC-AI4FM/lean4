module
public import TLAUniversal

open TLAUniversal Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TLAImported.«Counter»
@[expose] public noncomputable section
structure Constants where
def «Init» (c : Constants) (b : _root_.TLAUniversal.Behavior) (n : _root_.Nat) : _root_.TLAUniversal.Value :=
  (_root_.TLAUniversal.boolean (((b) (n) "x") = (_root_.TLAUniversal.integer 0)))
def «Next» (c : Constants) (b : _root_.TLAUniversal.Behavior) (n : _root_.Nat) : _root_.TLAUniversal.Value :=
  (_root_.TLAUniversal.boolean (((b) ((n) + 1) "x") = (_root_.TLAUniversal.realBinary (fun x y => x + y) ((b) (n) "x") (_root_.TLAUniversal.integer 1))))
def «Inv» (c : Constants) (b : _root_.TLAUniversal.Behavior) (n : _root_.Nat) : _root_.TLAUniversal.Value :=
  (_root_.TLAUniversal.realLessEqual (_root_.TLAUniversal.integer 0) ((b) (n) "x"))
def «Spec» (c : Constants) (b : _root_.TLAUniversal.Behavior) (n : _root_.Nat) : _root_.TLAUniversal.Value :=
  (_root_.TLAUniversal.boolean (_root_.TLAUniversal.truth (_root_.TLAImported.«Counter».«Init» c (b) (n)) ∧ _root_.TLAUniversal.truth (_root_.TLAUniversal.boolean (∀ z1 : _root_.Nat, (n) ≤ z1 → _root_.TLAUniversal.truth (_root_.TLAUniversal.boolean (_root_.TLAUniversal.truth (_root_.TLAImported.«Counter».«Next» c (b) (z1)) ∨ (((b) ((z1) + 1) "x") = ((b) (z1) "x"))))))))
end
end TLAImported.«Counter»

open TLAImported

namespace TLAImported.Counter
/-- The unchanged source specification preserves a nonnegative integer value. -/
theorem source_invariant (c : Constants) (b : Behavior)
    (h : truth (Spec c b 0)) : ∀ n, truth (Inv c b n) := by
  simp only [Spec, Init, Next, truth_boolean] at h
  have values : ∀ n : Nat, ∃ k : Nat, b n "x" = integer (k : Int) := by
    intro n
    induction n with
    | zero => exact ⟨0, h.1⟩
    | succ n ih =>
      obtain ⟨k, hk⟩ := ih
      rcases h.2 n (Nat.zero_le n) with step | stutter
      · refine ⟨k + 1, ?_⟩
        rw [hk, realBinary_add_integer] at step
        simpa only [Nat.cast_add, Nat.cast_one] using step
      · exact ⟨k, stutter.trans hk⟩
  intro n
  obtain ⟨k, hk⟩ := values n
  simp only [Inv, hk, realLessEqual_integer]
  exact Int.natCast_nonneg k
end TLAImported.Counter

namespace NativeCounterUniversal
open TLAImported

def Init : TLA.Predicate State := fun state => state "x" = integer 0
def Next : TLA.Action State := fun state next =>
  next "x" = realBinary (· + ·) (state "x") (integer 1)
def Inv : TLA.Predicate State := fun state => truth (realLessEqual (integer 0) (state "x"))
def Spec : TLA.Formula State := fun behavior time =>
  Init (behavior time) ∧
    TLA.always (TLA.action (TLA.square Next (fun state => state "x"))) behavior time

/-- Source import and native specification describe exactly the same behaviors. -/
theorem source_equivalence (c : Counter.Constants) (b : Behavior) (n : Nat) :
    truth (Counter.Spec c b n) ↔ Spec b n := by
  simp only [Counter.Spec, Counter.Init, Counter.Next, truth_boolean,
    Spec, Init, Next, TLA.always, TLA.action, TLA.square, TLA.unchanged]

example (c : Counter.Constants) (b : Behavior) (n : Nat) :
    Counter.Init c b n = liftPredicate Init b n := rfl

/-- A source proof can be reused by the equivalent Lean-native specification. -/
theorem safety (b : Behavior) (h : Spec b 0) : ∀ n, Inv (b n) := by
  have source := (source_equivalence {} b 0).mpr h
  intro n
  exact Counter.source_invariant {} b source n
end NativeCounterUniversal
