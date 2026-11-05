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
  · intro h
    obtain ⟨y, hy⟩ := h
    refine ⟨?_, ⟨y, hy⟩⟩
    apply ZFSet.mem_sUnion.mpr
    refine ⟨{x}, ?_, by simp⟩
    apply ZFSet.mem_sUnion.mpr
    exact ⟨ZFSet.pair x y, hy, by simp [ZFSet.pair]⟩

def update (f x y : Value) : Value :=
  function (domain f) (fun z => if z = x then y else apply f z)

theorem update_same (f x y : Value) (hx : x ∈ domain f) : apply (update f x y) x = y := by
  rw [update, apply_function _ _ _ hx]
  simp

def undefined : Value := choose (fun _ => False)

def intUnary (op : Int → Int) (x : Value) : Value :=
  if x ∈ ZFSet.Int then integer (op (toInt x)) else undefined

def intBinary (op : Int → Int → Int) (x y : Value) : Value :=
  if x ∈ ZFSet.Int ∧ y ∈ ZFSet.Int then integer (op (toInt x) (toInt y)) else undefined

def intCompare (op : Int → Int → Prop) (x y : Value) : Value :=
  boolean (x ∈ ZFSet.Int ∧ y ∈ ZFSet.Int ∧ op (toInt x) (toInt y))

def tuple (values : List Value) : Value :=
  function (interval (integer 1) (integer values.length))
    (fun index => values[(toInt index - 1).toNat]?.getD undefined)

def length (sequence : Value) : Value :=
  choose (fun n => n ∈ naturals ∧ domain sequence = interval (integer 1) n)

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

/-- A native specification over the same untyped value universe as source specifications. -/
def liftPredicate (p : State → Prop) : Expression := fun b n => boolean (p (b n))

def liftAction (a : State → State → Prop) : Expression :=
  fun b n => boolean (a (b n) (b (n + 1)))
end TLAUniversal
