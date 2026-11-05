/- Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license. -/
module
public import TLA.Basic
public import ZFLean.Booleans
public import TLAUniversal.Numbers
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public noncomputable section
namespace TLAUniversal
open Classical

abbrev Value := ZFSet.{0}
abbrev State := String → Value
abbrev Behavior := TLA.Behavior State
abbrev Expression := Behavior → Nat → Value

/-- Semantic locality of source expressions at the four SANY levels. -/
def expressionLevel (level : Nat) (e : Expression) : Prop :=
  match level with
  | 0 => ∀ b n c m, e b n = e c m
  | 1 => ∀ b n c m, b n = c m → e b n = e c m
  | 2 => ∀ b n c m, b n = c m → b (n + 1) = c (m + 1) → e b n = e c m
  | _ => ∀ b n c m,
      TLA.stutteringEquivalent (fun k => b (n + k)) (fun k => c (m + k)) → e b n = e c m

def truth (v : Value) : Prop := v = ZFSet.zftrue
def boolean (p : Prop) : Value := if p then ZFSet.zftrue else ZFSet.zffalse

theorem truth_boolean (p : Prop) : truth (boolean p) ↔ p := by
  simp only [truth, boolean]
  split_ifs with h
  · simp [h]
  · simp [h, Ne.symm ZFSet.zftrue_ne_zffalse]

abbrev real := Numeric.encode
abbrev toReal := Numeric.decode

theorem toReal_real (r : Real) : toReal (real r) = r := Numeric.decode_encode r

def reals : Value := ZFSet.range real

def integer (n : Int) : Value := real (n : Real)
def integers : Value := ZFSet.range integer

theorem integer_injective : Function.Injective integer := by
  intro a b h
  have eq := Numeric.encode_injective h
  exact_mod_cast eq

def toInt (v : Value) : Int := Classical.epsilon (fun n => integer n = v)

theorem integer_mem (n : Int) : integer n ∈ integers :=
  ZFSet.mem_range.mpr ⟨n, rfl⟩

theorem real_mem (r : Real) : real r ∈ reals :=
  ZFSet.mem_range.mpr ⟨r, rfl⟩

theorem integer_mem_real (n : Int) : integer n ∈ reals := real_mem (n : Real)

theorem toInt_integer (n : Int) : toInt (integer n) = n := by
  apply integer_injective
  exact Classical.epsilon_spec (p := fun x => integer x = integer n) ⟨n, rfl⟩

theorem toReal_integer (n : Int) : toReal (integer n) = (n : Real) :=
  Numeric.decode_encode (n : Real)

def naturals : Value := integers.sep (fun n => 0 ≤ toInt n)
def interval (lo hi : Value) : Value :=
  integers.sep (fun n => toInt lo ≤ toInt n ∧ toInt n ≤ toInt hi)

def enumerate (values : List Value) : Value := values.foldr Insert.insert ∅

theorem mem_enumerate (value : Value) (values : List Value) :
    value ∈ enumerate values ↔ value ∈ values := by
  induction values with
  | nil => simp [enumerate]
  | cons head tail ih =>
    simpa [enumerate] using (or_congr (Iff.refl (value = head)) ih)

theorem integer_mem_interval (value lo hi : Int) :
    integer value ∈ interval (integer lo) (integer hi) ↔ lo ≤ value ∧ value ≤ hi := by
  simp only [interval, ZFSet.mem_sep, integer_mem, toInt_integer, true_and]

theorem integer_mem_naturals (n : Int) : integer n ∈ naturals ↔ 0 ≤ n := by
  simp only [naturals, ZFSet.mem_sep, integer_mem, toInt_integer, true_and]

theorem mem_naturals (value : Value) : value ∈ naturals ↔ ∃ n : Nat, integer n = value := by
  constructor
  · intro h
    obtain ⟨hi, hn⟩ := ZFSet.mem_sep.mp h
    obtain ⟨k, rfl⟩ := ZFSet.mem_range.mp hi
    rw [toInt_integer] at hn
    exact ⟨k.toNat, congrArg integer (Int.toNat_of_nonneg hn)⟩
  · rintro ⟨n, rfl⟩
    exact (integer_mem_naturals _).mpr (by omega)

theorem interval_nat_injective (a b : Nat)
    (h : interval (integer 1) (integer a) = interval (integer 1) (integer b)) : a = b := by
  have bound : ∀ k l : Nat, interval (integer 1) (integer k) = interval (integer 1) (integer l) → k ≤ l := by
    intro k l eq
    by_cases hk : k = 0
    · omega
    · have member : integer k ∈ interval (integer 1) (integer k) :=
        (integer_mem_interval _ _ _).mpr ⟨by omega, by omega⟩
      rw [eq] at member
      have := (integer_mem_interval _ _ _).mp member
      omega
  exact Nat.le_antisymm (bound a b h) (bound b a h.symm)

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
  · intro h
    obtain ⟨y, hy⟩ := h
    refine ⟨?_, ⟨y, hy⟩⟩
    apply ZFSet.mem_sUnion.mpr
    refine ⟨{x}, ?_, by simp⟩
    apply ZFSet.mem_sUnion.mpr
    exact ⟨ZFSet.pair x y, hy, by simp [ZFSet.pair]⟩

theorem function_congr (set : Value) (f g : Value → Value)
    (h : ∀ x ∈ set, f x = g x) : function set f = function set g := by
  unfold function image
  apply congrArg ZFSet.range
  funext x
  exact congrArg (ZFSet.pair x.val) (h x.val x.property)

theorem domain_function (set : Value) (f : Value → Value) :
    domain (function set f) = set := by
  ext x
  rw [mem_domain]
  constructor
  · rintro ⟨y, hy⟩
    rw [function, mem_image] at hy
    obtain ⟨a, ha, eq⟩ := hy
    have h := (ZFSet.pair_inj.mp eq).1
    exact h ▸ ha
  · intro hx
    exact ⟨f x, (mem_image _ _ _).mpr ⟨x, hx, rfl⟩⟩

def update (f x y : Value) : Value :=
  function (domain f) (fun z => if z = x then y else apply f z)

theorem update_same (f x y : Value) (hx : x ∈ domain f) : apply (update f x y) x = y := by
  rw [update, apply_function _ _ _ hx]
  simp

def undefined : Value := choose (fun _ => False)

def intUnary (op : Int → Int) (x : Value) : Value :=
  if x ∈ integers then integer (op (toInt x)) else undefined

def intBinary (op : Int → Int → Int) (x y : Value) : Value :=
  if x ∈ integers ∧ y ∈ integers then integer (op (toInt x) (toInt y)) else undefined

def intCompare (op : Int → Int → Prop) (x y : Value) : Value :=
  boolean (x ∈ integers ∧ y ∈ integers ∧ op (toInt x) (toInt y))

def finite (set : Value) : Value := boolean (Finite set)

def cardinality (set : Value) : Value :=
  if Finite set then integer (Nat.card set) else undefined

def intPower (base exponent : Value) : Value :=
  if base ∈ integers ∧ exponent ∈ naturals then
    integer ((toInt base) ^ (toInt exponent).toNat)
  else undefined

def realUnary (op : Real → Real) (x : Value) : Value :=
  if x ∈ reals then real (op (toReal x)) else undefined

def realBinary (op : Real → Real → Real) (x y : Value) : Value :=
  if x ∈ reals ∧ y ∈ reals then real (op (toReal x) (toReal y)) else undefined

def realDivide (x y : Value) : Value :=
  if x ∈ reals ∧ y ∈ reals ∧ toReal y ≠ 0 then real (toReal x / toReal y) else undefined

def realPower (base exponent : Value) : Value :=
  if base ∈ reals ∧ exponent ∈ reals then
    real (Real.rpow (toReal base) (toReal exponent))
  else undefined

/-- The set of all real encodings is not itself one of those encodings. -/
def infinity : Value := reals

theorem infinity_not_real : infinity ∉ reals := ZFSet.mem_irrefl reals

def minusInfinity : Value := {infinity}

theorem minusInfinity_not_real : minusInfinity ∉ reals := by
  intro h
  exact ZFSet.mem_asymm h (by simp [minusInfinity, infinity])

theorem minusInfinity_ne_infinity : minusInfinity ≠ infinity := by
  intro h
  have member : infinity ∈ minusInfinity := by simp [minusInfinity]
  rw [h] at member
  exact ZFSet.mem_irrefl _ member

theorem real_ne_infinity (r : Real) : real r ≠ infinity := by
  intro h
  exact infinity_not_real (h ▸ real_mem r)

theorem real_ne_minusInfinity (r : Real) : real r ≠ minusInfinity := by
  intro h
  exact minusInfinity_not_real (h ▸ real_mem r)

/-- The numeric modules share real arithmetic, independently of which is imported. -/
def realSubtract (x y : Value) : Value :=
  if x ∈ reals then
    if y = infinity then minusInfinity
    else if y = minusInfinity then infinity
    else realBinary (fun a b => a - b) x y
  else undefined

def realNegate (x : Value) : Value := realSubtract (integer 0) x

def realLessEqual (x y : Value) : Value := boolean
  (if x ∈ reals ∧ y ∈ reals then toReal x ≤ toReal y
   else x = y ∨ (x = minusInfinity ∧ y ∈ reals) ∨
     ((x ∈ reals ∨ x = minusInfinity) ∧ y = infinity))

def realLess (x y : Value) : Value := boolean (truth (realLessEqual x y) ∧ x ≠ y)

/-- Integer intervals may have real or infinite endpoints. -/
def numberInterval (lo hi : Value) : Value :=
  integers.sep (fun n => truth (realLessEqual lo n) ∧ truth (realLessEqual n hi))

theorem realLessEqual_real (a b : Real) :
    truth (realLessEqual (real a) (real b)) ↔ a ≤ b := by
  simp [realLessEqual, truth_boolean, real_mem, toReal_real]

theorem realLessEqual_integer (a b : Int) :
    truth (realLessEqual (integer a) (integer b)) ↔ a ≤ b := by
  simp only [realLessEqual, truth_boolean, integer_mem_real, and_self, if_true, toReal_integer]
  norm_cast

theorem realLess_real_infinity (r : Real) : truth (realLess (real r) infinity) := by
  simp [realLess, realLessEqual, truth_boolean, real_mem, infinity_not_real, real_ne_infinity]

theorem realBinary_real (op : Real → Real → Real) (a b : Real) :
    realBinary op (real a) (real b) = real (op a b) := by
  unfold realBinary
  rw [if_pos ⟨real_mem a, real_mem b⟩, toReal_real, toReal_real]

theorem realBinary_add_integer (a b : Int) :
    realBinary (fun x y => x + y) (integer a) (integer b) = integer (a + b) := by
  simp [integer, realBinary_real, Int.cast_add]

theorem realBinary_mul_integer (a b : Int) :
    realBinary (fun x y => x * y) (integer a) (integer b) = integer (a * b) := by
  simp [integer, realBinary_real, Int.cast_mul]

theorem realSubtract_real (a b : Real) : realSubtract (real a) (real b) = real (a - b) := by
  simp [realSubtract, real_mem, real_ne_infinity, real_ne_minusInfinity, realBinary_real]

theorem realNegate_integer (a : Int) : realNegate (integer a) = integer (-a) := by
  simp [realNegate, integer, realSubtract_real]

theorem realNegate_infinity : realNegate infinity = minusInfinity := by
  simp [realNegate, realSubtract, integer_mem_real]

theorem realNegate_minusInfinity : realNegate minusInfinity = infinity := by
  simp [realNegate, realSubtract, integer_mem_real, minusInfinity_ne_infinity]

theorem realLess_minusInfinity_real (r : Real) : truth (realLess minusInfinity (real r)) := by
  simp [realLess, realLessEqual, truth_boolean, minusInfinity_not_real, real_mem,
    Ne.symm (real_ne_minusInfinity r)]

theorem realPower_real (a b : Real) : realPower (real a) (real b) = real (Real.rpow a b) := by
  simp [realPower, real_mem, toReal_real]

def tuple (values : List Value) : Value :=
  function (interval (integer 1) (integer values.length))
    (fun index => values[(toInt index - 1).toNat]?.getD undefined)

theorem apply_tuple (values : List Value) (index : Nat) (h : index < values.length) :
    apply (tuple values) (integer ((index : Int) + 1)) = values[index] := by
  unfold tuple
  rw [apply_function]
  · simp [toInt_integer, h]
  · apply (integer_mem_interval _ _ _).mpr
    omega

def length (sequence : Value) : Value :=
  choose (fun n => n ∈ naturals ∧ domain sequence = interval (integer 1) n)

theorem length_tuple (values : List Value) : length (tuple values) = integer values.length := by
  have witness : integer values.length ∈ naturals ∧
      domain (tuple values) = interval (integer 1) (integer values.length) := by
    exact ⟨(integer_mem_naturals _).mpr (by omega), domain_function _ _⟩
  have chosen := choose_spec
    (fun n => n ∈ naturals ∧ domain (tuple values) = interval (integer 1) n)
    ⟨integer values.length, witness⟩
  change length (tuple values) ∈ naturals ∧
    domain (tuple values) = interval (integer 1) (length (tuple values)) at chosen
  obtain ⟨k, hk⟩ := (mem_naturals _).mp chosen.1
  have domains := chosen.2
  rw [← hk, witness.2] at domains
  have equal := interval_nat_injective values.length k domains
  rw [← hk, ← equal]

def sequences (elements : Value) : Value :=
  ZFSet.sUnion (ZFSet.range (fun n : Nat => (interval (integer 1) (integer n)).funs elements))

def append (sequence value : Value) : Value :=
  function (interval (integer 1) (integer (toInt (length sequence) + 1)))
    (fun i => if toInt i = toInt (length sequence) + 1 then value else apply sequence i)

def concatenate (left right : Value) : Value :=
  function (interval (integer 1) (integer (toInt (length left) + toInt (length right))))
    (fun i => if toInt i ≤ toInt (length left) then apply left i
      else apply right (integer (toInt i - toInt (length left))))

def prepend (value sequence : Value) : Value :=
  function (interval (integer 1) (integer (toInt (length sequence) + 1)))
    (fun i => if toInt i = 1 then value else apply sequence (integer (toInt i - 1)))

def cartesian : List Value → Value
  | [] => enumerate [tuple []]
  | first :: rest => ZFSet.sUnion (image first (fun x => image (cartesian rest) (prepend x)))

def caseValue (clauses : List (Value × Value)) (fallback : Value) : Value :=
  if ∃ clause ∈ clauses, truth clause.1 then
    choose (fun value => ∃ clause ∈ clauses, truth clause.1 ∧ value = clause.2)
  else fallback

theorem caseValue_spec (clauses : List (Value × Value)) (fallback : Value)
    (h : ∃ clause ∈ clauses, truth clause.1) :
    ∃ clause ∈ clauses, truth clause.1 ∧ caseValue clauses fallback = clause.2 := by
  unfold caseValue
  rw [if_pos h]
  have witness : ∃ value, ∃ clause ∈ clauses, truth clause.1 ∧ value = clause.2 := by
    obtain ⟨clause, member, guard⟩ := h
    exact ⟨clause.2, clause, member, guard, rfl⟩
  exact choose_spec _ witness

def subsequence (sequence lo hi : Value) : Value :=
  function (interval (integer 1) (integer (max 0 (toInt hi - toInt lo + 1))))
    (fun i => apply sequence (integer (toInt lo + toInt i - 1)))

def string (text : String) : Value :=
  tuple (text.toList.map (fun c => ZFSet.pair (integer (-1)) (integer c.toNat)))

def strings : Value := ZFSet.range string

def record (fields : List (String × Value)) : Value :=
  function (enumerate (fields.map (fun field => string field.1)))
    (fun key => choose (fun value => ∃ field ∈ fields, key = string field.1 ∧ value = field.2))

def recordSpace (fields : List (String × Value)) : Value :=
  ((enumerate (fields.map (fun field => string field.1))).funs
    (ZFSet.sUnion (enumerate (fields.map Prod.snd)))).sep
      (fun f => ∀ field ∈ fields, apply f (string field.1) ∈ field.2)

def selectPath (value : Value) (keys : List Value) : Value :=
  keys.foldl apply value

def updatePath (value : Value) (keys : List Value) (replacement : Value) : Value :=
  match keys with
  | [] => replacement
  | key :: rest => update value key (updatePath (apply value key) rest replacement)

theorem intBinary_integer (op : Int → Int → Int) (a b : Int) :
    intBinary op (integer a) (integer b) = integer (op a b) := by
  unfold intBinary
  rw [if_pos ⟨integer_mem a, integer_mem b⟩, toInt_integer, toInt_integer]

/-- Gonthier–Lamport's fixing condition, including agreement outside recursive calls. -/
def fixes (body : Value → Value → Value) (g : Value) : Prop :=
  ∀ h : Value, (∀ x ∈ domain g, apply h x = apply g x) →
    g = function (domain g) (fun x => body x h)

/-- Recursive operators choose a fixing graph containing the actual argument.
See https://lamport.azurewebsites.net/pubs/recursive-ops.pdf, section 3.1. -/
def recursiveOperator (body : Value → Value → Value) (x : Value) : Value :=
  apply (choose (fun g => x ∈ domain g ∧ fixes body g)) x

theorem recursiveOperator_witness (body : Value → Value → Value) (x : Value)
    (existsGraph : ∃ g, x ∈ domain g ∧ fixes body g) :
    ∃ g, x ∈ domain g ∧ fixes body g ∧ recursiveOperator body x = apply g x := by
  have h := choose_spec (fun g => x ∈ domain g ∧ fixes body g) existsGraph
  exact ⟨_, h.1, h.2, rfl⟩

theorem recursiveOperator_base (body : Value → Value → Value) (x value : Value)
    (base : ∀ g, body x g = value) : recursiveOperator body x = value := by
  have witness : ∃ g, x ∈ domain g ∧ fixes body g := by
    refine ⟨function {x} (fun _ => value), ?_, ?_⟩
    · rw [domain_function]
      simp
    · intro h _
      rw [domain_function]
      apply function_congr
      intro y hy
      have eq : y = x := by simpa using hy
      subst y
      exact (base h).symm
  obtain ⟨g, hx, hg, result⟩ := recursiveOperator_witness body x witness
  rw [result]
  have eq := hg g (by intro y _; rfl)
  calc
    apply g x = apply (function (domain g) (fun y => body y g)) x :=
      congrArg (fun f => apply f x) eq
    _ = body x g := apply_function _ _ _ hx
    _ = value := base g

theorem recursiveOperator_constant (value x : Value) :
    recursiveOperator (fun _ _ => value) x = value := by
  have witness : ∃ g, x ∈ domain g ∧ fixes (fun _ _ => value) g := by
    refine ⟨function {x} (fun _ => value), ?_, ?_⟩
    · rw [domain_function]
      simp
    · intro h _
      rw [domain_function]
  obtain ⟨g, hx, hg, result⟩ := recursiveOperator_witness (fun _ _ => value) x witness
  rw [result]
  have eq := hg g (by intro y _; rfl)
  calc
    apply g x = apply (function (domain g) (fun _ => value)) x :=
      congrArg (fun f => apply f x) eq
    _ = value := apply_function _ _ _ hx

/-- A native specification over the same untyped value universe as source specifications. -/
def liftPredicate (p : State → Prop) : Expression := fun b n => boolean (p (b n))

def liftAction (a : State → State → Prop) : Expression :=
  fun b n => boolean (a (b n) (b (n + 1)))
end TLAUniversal
