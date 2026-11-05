/- Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license. -/
module
public import TLAUniversal.Values

@[expose] public noncomputable section
namespace TLAUniversal
open Classical

theorem function_isFunc (D E : Value) (f : Value → Value)
    (h : ∀ x ∈ D, f x ∈ E) : ZFSet.IsFunc D E (function D f) := by
  constructor
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := (mem_image _ _ _).mp hp
    exact ZFSet.pair_mem_prod.mpr ⟨hx, h x hx⟩
  · intro x hx
    refine ⟨f x, (mem_image _ _ _).mpr ⟨x, hx, rfl⟩, ?_⟩
    intro y hy
    obtain ⟨z, _, pair_eq⟩ := (mem_image _ _ _).mp hy
    obtain ⟨rfl, value_eq⟩ := ZFSet.pair_inj.mp pair_eq
    exact value_eq.symm

theorem domain_isFunc {D E f : Value} (hf : ZFSet.IsFunc D E f) : domain f = D := by
  apply ZFSet.ext
  intro x
  rw [mem_domain]
  constructor
  · rintro ⟨y, hy⟩
    exact (ZFSet.pair_mem_prod.mp (hf.1 hy)).1
  · intro hx
    obtain ⟨y, hy, _⟩ := hf.2 x hx
    exact ⟨y, hy⟩

theorem pair_apply_isFunc {D E f x : Value} (hf : ZFSet.IsFunc D E f) (hx : x ∈ D) :
    ZFSet.pair x (apply f x) ∈ f := by
  obtain ⟨y, hy, _⟩ := hf.2 x hx
  exact choose_spec (fun y => ZFSet.pair x y ∈ f) ⟨y, hy⟩

theorem apply_mem {D E f x : Value} (hf : ZFSet.IsFunc D E f) (hx : x ∈ D) :
    apply f x ∈ E :=
  (ZFSet.pair_mem_prod.mp (hf.1 (pair_apply_isFunc hf hx))).2

theorem function_eta {D E f : Value} (hf : ZFSet.IsFunc D E f) :
    f = function D (fun x => apply f x) := by
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.mp (hf.1 hp)
    obtain ⟨w, _, unique⟩ := hf.2 x hx
    have eq : apply f x = y :=
      (unique _ (pair_apply_isFunc hf hx)).trans (unique _ hp).symm
    exact (mem_image _ _ _).mpr ⟨x, hx, congrArg (ZFSet.pair x) eq⟩
  · intro hp
    obtain ⟨x, hx, rfl⟩ := (mem_image _ _ _).mp hp
    exact pair_apply_isFunc hf hx

theorem function_ext {D E F f g : Value} (hf : ZFSet.IsFunc D E f)
    (hg : ZFSet.IsFunc D F g) (eq : ∀ x ∈ D, apply f x = apply g x) : f = g := by
  rw [function_eta hf, function_eta hg]
  exact function_congr D _ _ eq

theorem function_isFunc_iff (D E A : Value) (f : Value → Value) :
    ZFSet.IsFunc D E (function A f) ↔ D = A ∧ ∀ x ∈ D, f x ∈ E := by
  constructor
  · intro h
    have hd : D = A := (domain_isFunc h).symm.trans (domain_function A f)
    refine ⟨hd, ?_⟩
    intro x hx
    have member := apply_mem h hx
    rw [apply_function A f x (hd ▸ hx)] at member
    exact member
  · rintro ⟨rfl, h⟩
    exact function_isFunc _ _ _ h

theorem domain_update (f x y : Value) : domain (update f x y) = domain f :=
  domain_function _ _

theorem update_other (f x y z : Value) (hz : z ∈ domain f) (hne : z ≠ x) :
    apply (update f x y) z = apply f z := by
  simp [update, apply_function _ _ _ hz, hne]

end TLAUniversal
