module
import TLA
/-! Extensional sets, partial-domain functions, choice and sequence laws. -/
open TLA

example : Data.Set.mem (2 : Int) (Data.Set.enumerate [1, 2, 3]) := by simp [Data.Set.mem, Data.Set.enumerate]
example : Data.Set.subset (Data.Set.enumerate [1, 2]) (Data.Set.enumerate [1, 2, 3]) := by
  intro x hx
  simp [Data.Set.enumerate] at *
  rcases hx with rfl | rfl <;> simp
example : Data.Set.mem (Data.Set.enumerate [1, 2])
    (Data.Set.power (Data.Set.enumerate [1, 2, 3])) := by
  intro x hx
  simp [Data.Set.enumerate] at *
  rcases hx with rfl | rfl <;> simp

noncomputable def f : Data.Function Int Int :=
  Data.Function.make (fun i => 1 ≤ i ∧ i ≤ 3) (fun i => i * 2)

example : Data.Function.apply f 2 = 4 := by
  simp [f, Data.Function.apply, Data.Function.make]
example : Data.Function.apply (Data.Function.update f 2 7) 2 = 7 := by
  simp [f, Data.Function.apply, Data.Function.update, Data.Function.make]
example : Data.Function.apply (Data.Function.update f 2 7) 1 = 2 := by
  simp [f, Data.Function.apply, Data.Function.update, Data.Function.make]
example : (Data.Function.update f 8 7).domain = f.domain := rfl

example : Data.Set.choose (fun n : Nat => n = 3) = 3 := by
  exact Data.Set.choose_spec (fun n : Nat => n = 3) ⟨3, rfl⟩
example : Data.Seq.len ([1, 2, 3] : List Int) = 3 := rfl
example : Data.Seq.get ([1, 2, 3] : List Int) 1 = 1 := rfl
example : Data.Seq.subseq ([1, 2, 3, 4] : List Int) 2 3 = [2, 3] := rfl
