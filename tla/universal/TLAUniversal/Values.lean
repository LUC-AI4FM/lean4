/- Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license. -/
module
public import TLA.Basic
public import ZFLean.Booleans
public import ZFLean.Integers

@[expose] public noncomputable section
namespace TLAUniversal
open Classical

abbrev Value := ZFSet.{0}
abbrev State := String → Value
abbrev Behavior := TLA.Behavior State
abbrev Expression := Behavior → Nat → Value

def truth (v : Value) : Prop := v = ZFSet.zftrue
def boolean (p : Prop) : Value := if p then ZFSet.zftrue else ZFSet.zffalse

theorem truth_boolean (p : Prop) : truth (boolean p) ↔ p := by
  simp only [truth, boolean]
  split_ifs with h
  · simp [h]
  · simp [h, Ne.symm ZFSet.zftrue_ne_zffalse]

def integer (n : Int) : Value := (ZFSet.ZFInt.into (n : ZFSet.ZFInt)).val

def toInt (v : Value) : Int :=
  if h : v ∈ ZFSet.Int then
    ZFSet.ZFInt.equivInt (ZFSet.ZFInt.outof ⟨v, h⟩)
  else 0

theorem integer_mem (n : Int) : integer n ∈ ZFSet.Int :=
  (ZFSet.ZFInt.into (n : ZFSet.ZFInt)).property

theorem toInt_integer (n : Int) : toInt (integer n) = n := by
  unfold toInt
  rw [dif_pos (integer_mem n)]
  change ZFSet.ZFInt.equivInt (ZFSet.ZFInt.outof (ZFSet.ZFInt.into (n : ZFSet.ZFInt))) = n
  rw [ZFSet.ZFInt.outof_into, ZFSet.ZFInt.equivInt_intCast]

def naturals : Value := ZFSet.Int.sep (fun n => 0 ≤ toInt n)
def interval (lo hi : Value) : Value :=
  ZFSet.Int.sep (fun n => toInt lo ≤ toInt n ∧ toInt n ≤ toInt hi)

def enumerate (values : List Value) : Value := values.foldr Insert.insert ∅

def image (domain : Value) (f : Value → Value) : Value :=
  ZFSet.range (fun x : domain => f x.val)

theorem mem_image (domain : Value) (f : Value → Value) (y : Value) :
    y ∈ image domain f ↔ ∃ x ∈ domain, f x = y := by
  simp [image]

def choose (p : Value → Prop) : Value := Classical.epsilon p

theorem choose_spec (p : Value → Prop) (h : ∃ x, p x) : p (choose p) :=
  Classical.epsilon_spec h

def function (domain : Value) (f : Value → Value) : Value :=
  image domain (fun x => ZFSet.pair x (f x))

def apply (f x : Value) : Value := choose (fun y => ZFSet.pair x y ∈ f)

theorem apply_function (domain : Value) (f : Value → Value) (x : Value)
    (hx : x ∈ domain) : apply (function domain f) x = f x := by
  have existsValue : ∃ y, ZFSet.pair x y ∈ function domain f := by
    exact ⟨f x, (mem_image _ _ _).mpr ⟨x, hx, rfl⟩⟩
  have h := choose_spec (fun y => ZFSet.pair x y ∈ function domain f) existsValue
  change ZFSet.pair x (apply (function domain f) x) ∈ function domain f at h
  rw [function, mem_image] at h
  obtain ⟨a, _, ha⟩ := h
  obtain ⟨rfl, value⟩ := ZFSet.pair_inj.mp ha
  exact value.symm

def domain (f : Value) : Value :=
  (ZFSet.sUnion (ZFSet.sUnion f)).sep (fun x => ∃ y, ZFSet.pair x y ∈ f)

theorem mem_domain (f x : Value) : x ∈ domain f ↔ ∃ y, ZFSet.pair x y ∈ f := by
  rw [domain, ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro h@⟨y, hy⟩
    refine ⟨?_, h⟩
    apply ZFSet.mem_sUnion.mpr
    refine ⟨{x}, ?_, by simp⟩
    apply ZFSet.mem_sUnion.mpr
    exact ⟨ZFSet.pair x y, hy, by simp [ZFSet.pair]⟩

def update (f x y : Value) : Value :=
  function (domain f) (fun z => if z = x then y else apply f z)

theorem update_same (f x y : Value) (hx : x ∈ domain f) : apply (update f x y) x = y := by
  rw [update, apply_function _ _ _ hx]
  simp

/-- A native specification over the same untyped value universe as source specifications. -/
def liftPredicate (p : State → Prop) : Expression := fun b n => boolean (p (b n))

def liftAction (a : State → State → Prop) : Expression :=
  fun b n => boolean (a (b n) (b (n + 1)))
end TLAUniversal
