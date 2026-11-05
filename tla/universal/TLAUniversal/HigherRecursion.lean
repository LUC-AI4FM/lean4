/- Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license. -/
module
public import TLAUniversal.Values

@[expose] public noncomputable section
namespace TLAUniversal
universe u

/-- A partial graph over an argument type that may contain operator parameters. -/
structure HigherGraph (α : Type u) where
  carrier : Set α
  values : α → Value

/-- The fixing condition for operator-valued as well as value-valued arguments.
The body must have the same result for every extension of the partial graph. -/
def higherFixes {α : Type u} (body : α → (α → Value) → Value)
    (graph : HigherGraph α) : Prop :=
  ∀ candidate, (∀ x ∈ graph.carrier, candidate x = graph.values x) →
    ∀ x ∈ graph.carrier, body x candidate = graph.values x

/-- Class-level fixing graphs support higher-order recursive arguments without
encoding functions as ZFC values or postulating recursive equations. -/
def higherRecursiveOperator {α : Type u} (body : α → (α → Value) → Value)
    (x : α) : Value :=
  if h : ∃ graph : HigherGraph α, x ∈ graph.carrier ∧ higherFixes body graph then
    (Classical.choose h).values x
  else undefined

theorem higherRecursiveOperator_witness {α : Type u}
    (body : α → (α → Value) → Value) (x : α)
    (existsGraph : ∃ graph : HigherGraph α, x ∈ graph.carrier ∧ higherFixes body graph) :
    ∃ graph : HigherGraph α, x ∈ graph.carrier ∧ higherFixes body graph ∧
      higherRecursiveOperator body x = graph.values x := by
  refine ⟨Classical.choose existsGraph, (Classical.choose_spec existsGraph).1,
    (Classical.choose_spec existsGraph).2, ?_⟩
  simp only [higherRecursiveOperator, dif_pos existsGraph]

theorem higherRecursiveOperator_base {α : Type u}
    (body : α → (α → Value) → Value) (x : α) (value : Value)
    (base : ∀ candidate, body x candidate = value) :
    higherRecursiveOperator body x = value := by
  have witness : ∃ graph : HigherGraph α, x ∈ graph.carrier ∧ higherFixes body graph := by
    refine ⟨⟨{x}, fun _ => value⟩, by simp, ?_⟩
    intro candidate _ y hy
    have eq : y = x := by simpa using hy
    subst y
    exact base candidate
  obtain ⟨graph, hx, fixing, result⟩ := higherRecursiveOperator_witness body x witness
  rw [result]
  exact (fixing graph.values (by intro y _; rfl) x hx).symm.trans (base graph.values)

end TLAUniversal
