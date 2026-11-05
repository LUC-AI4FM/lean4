/- Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license. -/
module
public import TLAUniversal.Values

@[expose] public noncomputable section
namespace TLAUniversal

theorem natural_induction (p : Value → Prop)
    (base : p (integer 0))
    (step : ∀ x ∈ naturals, p x → p (realBinary (· + ·) x (integer 1))) :
    ∀ x ∈ naturals, p x := by
  have all : ∀ n : Nat, p (integer n) := by
    intro n
    induction n with
    | zero => exact base
    | succ n ih =>
      have next := step (integer n) ((integer_mem_naturals _).mpr (by omega)) ih
      simpa only [realBinary_add_integer, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using next
  intro x hx
  obtain ⟨n, rfl⟩ := (mem_naturals x).mp hx
  exact all n

end TLAUniversal
