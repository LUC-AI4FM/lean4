module
import TLA
/-! Action composition and stuttering-aware flexible quantification. -/
example : TLA.compose (fun x y : Int => y = x + 1) (fun x y => y = x + 1) 0 2 := by
  exact ⟨1, rfl, rfl⟩
example (b : TLA.Behavior Int) : TLA.stutteringEquivalent b b :=
  TLA.stutteringEquivalent_refl b
example (b : TLA.Behavior Int) :
    TLA.existsFlexible (fun h => fun c n => h n = c n) b 0 := by
  apply TLA.existsFlexible_intro (h := b)
  rfl
example (b : TLA.Behavior Int) : TLA.guarantees (fun _ _ => False) (fun _ _ => True) b 0 :=
  TLA.guarantees_true _ _ _
