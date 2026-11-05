/- Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license. -/
module
public import ZFLean.Integers
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public noncomputable section
namespace TLAUniversal.Numeric
open Classical

private def intCode (n : Int) : ZFSet.{0} := (ZFSet.ZFInt.into (n : ZFSet.ZFInt)).val

private theorem intCode_injective : Function.Injective intCode := by
  intro a b h
  have hsub : ZFSet.ZFInt.into (a : ZFSet.ZFInt) = ZFSet.ZFInt.into (b : ZFSet.ZFInt) :=
    Subtype.ext h
  have eq := congrArg (fun x => ZFSet.ZFInt.equivInt (ZFSet.ZFInt.outof x)) hsub
  simpa only [ZFSet.ZFInt.outof_into, ZFSet.ZFInt.equivInt_intCast] using eq

private def ratCode (q : Rat) : ZFSet.{0} := ZFSet.pair (intCode q.num) (intCode q.den)

private theorem ratCode_injective : Function.Injective ratCode := by
  intro a b h
  obtain ⟨hn, hd⟩ := ZFSet.pair_inj.mp h
  apply Rat.ext (intCode_injective hn)
  exact_mod_cast intCode_injective hd

/-- A real is encoded by its rational lower cut; all numeric subtypes share it. -/
def encode (r : Real) : ZFSet.{0} :=
  ZFSet.range (fun q : {q : Rat // (q : Real) < r} => ratCode q.val)

private theorem mem_encode (q : Rat) (r : Real) : ratCode q ∈ encode r ↔ (q : Real) < r := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := ZFSet.mem_range.mp h
    have eq := ratCode_injective ha
    exact eq ▸ a.property
  · intro h
    exact ZFSet.mem_range.mpr ⟨⟨q, h⟩, rfl⟩

theorem encode_injective : Function.Injective encode := by
  intro a b h
  apply le_antisymm
  · by_contra hn
    obtain ⟨q, hb, ha⟩ := exists_rat_btwn (lt_of_not_ge hn)
    have member := (mem_encode q a).mpr ha
    rw [h] at member
    exact (not_lt_of_ge (le_of_lt hb)) ((mem_encode q b).mp member)
  · by_contra hn
    obtain ⟨q, ha, hb⟩ := exists_rat_btwn (lt_of_not_ge hn)
    have member := (mem_encode q b).mpr hb
    rw [← h] at member
    exact (not_lt_of_ge (le_of_lt ha)) ((mem_encode q a).mp member)

def decode (value : ZFSet.{0}) : Real := Classical.epsilon (fun r => encode r = value)

theorem decode_encode (r : Real) : decode (encode r) = r := by
  apply encode_injective
  exact Classical.epsilon_spec (p := fun x => encode x = encode r) ⟨r, rfl⟩

end TLAUniversal.Numeric
