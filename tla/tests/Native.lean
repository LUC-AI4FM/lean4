module
import TLA
/-! Native specifications, stuttering, invariants, and temporal boundary cases. -/
namespace NativeCounter

def Init : TLA.Predicate Int := fun x => x = 0
def Next : TLA.Action Int := fun x y => y = x + 1
def Safe : TLA.Predicate Int := fun x => 0 ≤ x

theorem safety (b : TLA.Behavior Int) (h : TLA.spec Init Next b 0) :
    TLA.always (TLA.state Safe) b 0 := by
  apply TLA.invariant Init Safe Next ?_ ?_ b h
  · intro s hs
    simp [Init] at hs
    simp [Safe, hs]
  · intro s t hs hn
    simp [Safe] at *
    simp [Next] at hn
    omega

example : TLA.spec Init Next (fun _ => 0) 0 := by
  constructor
  · rfl
  · intro n _
    exact Or.inr rfl

example : ¬ TLA.eventually (TLA.state (fun x : Int => x = 1)) (fun _ => 0) 0 := by
  rintro ⟨n, _, hn⟩
  change (0 : Int) = 1 at hn
  contradiction

example : ¬ TLA.weakFairness Next id (fun _ => 0) 0 := by
  intro h
  have enabled : TLA.eventually (TLA.always (TLA.state (TLA.enabled (TLA.angle Next id))))
      (fun _ => 0) 0 := by
    refine ⟨0, Nat.le_refl _, ?_⟩
    intro n _
    exact ⟨1, by simp [Next], by simp [TLA.unchanged]⟩
  obtain ⟨n, _, hn⟩ := h enabled 0 (Nat.le_refl _)
  have impossible := hn.2
  exact impossible rfl
end NativeCounter
