/- Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license. -/
module

@[expose] public section
namespace TLA.Data
abbrev Set (α : Type u) := α → Prop

namespace Set
variable {α : Type u} {β : Type v}
def mem (x : α) (s : Set α) : Prop := s x
def empty : Set α := fun _ => False
def enumerate (xs : List α) : Set α := fun x => x ∈ xs
def subset (s t : Set α) : Prop := ∀ x, s x → t x
def union (s t : Set α) : Set α := fun x => s x ∨ t x
def inter (s t : Set α) : Set α := fun x => s x ∧ t x
def diff (s t : Set α) : Set α := fun x => s x ∧ ¬ t x
def filter (s : Set α) (p : α → Prop) : Set α := fun x => s x ∧ p x
def image (s : Set α) (f : α → β) : Set β := fun y => ∃ x, s x ∧ f x = y
def power (s : Set α) : Set (Set α) := fun t => subset t s
def bigUnion (ss : Set (Set α)) : Set α := fun x => ∃ s, ss s ∧ s x
noncomputable def choose [Inhabited α] (p : α → Prop) : α := Classical.epsilon p

theorem choose_spec [Inhabited α] (p : α → Prop) (h : ∃ x, p x) : p (choose p) :=
  Classical.epsilon_spec h

theorem ext (s t : Set α) (h : ∀ x, s x ↔ t x) : s = t := by
  funext x
  exact propext (h x)

def naturals : Set Int := fun x => 0 ≤ x
def integers : Set Int := fun _ => True
def interval (lo hi : Int) : Set Int := fun x => lo ≤ x ∧ x ≤ hi
end Set

/-- A function's values exist only on its domain, so equality ignores other inputs. -/
structure Function (α : Type u) (β : Type v) where
  domain : Set α
  value : {x // domain x} → β

namespace Function
variable {α : Type u} {β : Type v}
def make (domain : Set α) (value : α → β) : Function α β :=
  ⟨domain, fun x => value x.val⟩
noncomputable def apply [Inhabited β] (f : Function α β) (x : α) : β := by
  classical
  exact if h : f.domain x then f.value ⟨x, h⟩ else default
noncomputable def update (f : Function α β) (x : α) (y : β) : Function α β := by
  classical
  exact ⟨f.domain, fun z => if z.val = x then y else f.value z⟩
def space (s : Set α) (t : Set β) : Set (Function α β) :=
  fun f => f.domain = s ∧ ∀ x, t (f.value x)

theorem ext (f g : Function α β) (hd : f.domain = g.domain)
    (hv : ∀ x hx hy, f.value ⟨x, hx⟩ = g.value ⟨x, hy⟩) : f = g := by
  cases f with
  | mk fd fv =>
    cases g with
    | mk gd gv =>
      simp only at hd
      subst gd
      congr
      funext x
      exact hv x.val x.property x.property
end Function

namespace Seq
variable {α : Type u}
def space (s : Set α) : Set (List α) := fun xs => ∀ x ∈ xs, s x
def len (xs : List α) : Int := xs.length
/-- TLA+ sequence indexing starts at one; out-of-domain values are unspecified. -/
def get [Inhabited α] (xs : List α) (i : Int) : α :=
  if 1 ≤ i then xs[(i - 1).toNat]?.getD default else default
def subseq (xs : List α) (lo hi : Int) : List α :=
  (xs.drop (lo - 1).toNat).take (hi - lo + 1).toNat
end Seq
end TLA.Data
