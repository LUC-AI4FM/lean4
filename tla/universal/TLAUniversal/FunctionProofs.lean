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

theorem function_range_mono {domain source target f : Value}
    (hf : ZFSet.IsFunc domain source f) (included : source ⊆ target) :
    ZFSet.IsFunc domain target f := by
  constructor
  · intro p hp
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.mp (hf.1 hp)
    exact ZFSet.pair_mem_prod.mpr ⟨hx, included hy⟩
  · exact hf.2

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

theorem function_range_of_values {D E F f : Value} (hf : ZFSet.IsFunc D E f)
    (values : ∀ x ∈ D, apply f x ∈ F) : ZFSet.IsFunc D F f := by
  rw [function_eta hf]
  exact function_isFunc D F (fun x => apply f x) values

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

theorem domain_updatePath_cons (value key replacement : Value) (rest : List Value) :
    domain (updatePath value (key :: rest) replacement) = domain value := by
  simp only [updatePath, domain_update]

theorem apply_updatePath_other (value key replacement field : Value) (rest : List Value)
    (member : field ∈ domain value) (different : field ≠ key) :
    apply (updatePath value (key :: rest) replacement) field = apply value field := by
  simp only [updatePath, update_other _ _ _ _ member different]

theorem apply_updatePath_single (value key replacement : Value)
    (member : key ∈ domain value) :
    apply (updatePath value [key] replacement) key = replacement := by
  simp only [updatePath, update_same _ _ _ member]

theorem update_isFunc {D E f key value : Value}
    (hf : ZFSet.IsFunc D E f) (hv : value ∈ E) :
    ZFSet.IsFunc D E (update f key value) := by
  rw [update, domain_isFunc hf]
  apply function_isFunc
  intro x hx
  split_ifs
  · exact hv
  · exact apply_mem hf hx

theorem singleton_range_isFunc {D E f value : Value}
    (hf : ZFSet.IsFunc D (enumerate [value]) f) (hv : value ∈ E) :
    ZFSet.IsFunc D E f := by
  apply function_range_mono hf
  intro x hx
  have eq : x = value := by simpa only [mem_enumerate, List.mem_singleton] using hx
  simpa only [eq] using hv

theorem subset_intro {A B : Value} (h : ∀ x, x ∈ A → x ∈ B) : A ⊆ B := h

theorem subset_member {A B x : Value} (h : A ⊆ B) (hx : x ∈ A) : x ∈ B := h hx

theorem union_subset_iff (A B C : Value) :
    A ∪ B ⊆ C ↔ A ⊆ C ∧ B ⊆ C := by
  constructor
  · intro h
    exact ⟨fun _ hx => h (ZFSet.mem_union.mpr (Or.inl hx)),
      fun _ hx => h (ZFSet.mem_union.mpr (Or.inr hx))⟩
  · rintro ⟨ha, hb⟩ x hx
    exact (ZFSet.mem_union.mp hx).elim (ha ·) (hb ·)

theorem enumerate_subset_iff (values : List Value) (target : Value) :
    enumerate values ⊆ target ↔ ∀ x ∈ values, x ∈ target := by
  constructor
  · intro h x hx
    exact h ((mem_enumerate _ _).mpr hx)
  · intro h x hx
    exact h x ((mem_enumerate _ _).mp hx)

theorem domain_tuple (values : List Value) :
    domain (tuple values) = interval (integer 1) (integer values.length) :=
  domain_function _ _

theorem apply_tuple_at (values : List Value) (i : Int)
    (h : 1 ≤ i ∧ i ≤ values.length) :
    apply (tuple values) (integer i) = values[(i - 1).toNat]?.getD undefined := by
  unfold tuple
  rw [apply_function _ _ _ ((integer_mem_interval _ _ _).mpr h)]
  rw [toInt_integer]

theorem tuple_injective : Function.Injective tuple := by
  intro xs ys eq
  have domains := congrArg domain eq
  rw [domain_tuple, domain_tuple] at domains
  have lengths := interval_nat_injective xs.length ys.length domains
  apply List.ext_getElem lengths
  intro i hx hy
  have point := congrArg (fun f => apply f (integer ((i : Int) + 1))) eq
  rw [apply_tuple xs i hx, apply_tuple ys i hy] at point
  exact point

theorem tuple_eq_iff (xs ys : List Value) : tuple xs = tuple ys ↔ xs = ys :=
  tuple_injective.eq_iff

theorem string_injective : Function.Injective string := by
  intro a b eq
  apply String.toList_injective
  have mapped := tuple_injective eq
  apply (List.map_inj_right (fun x y h => ?_)).mp mapped
  apply Char.toNat_inj.mp
  have integers := integer_injective (ZFSet.pair_inj.mp h).2
  exact_mod_cast integers

theorem string_eq_iff (a b : String) : string a = string b ↔ a = b :=
  string_injective.eq_iff

theorem string_mem (s : String) : string s ∈ strings :=
  ZFSet.mem_range.mpr ⟨s, rfl⟩

theorem domain_record (fields : List (String × Value)) :
    domain (record fields) = enumerate (fields.map (fun field => string field.1)) :=
  domain_function _ _

-- Equality of records preserves every field name, independent of field values.
-- Keep the quantifiers bounded by the literal field lists so normalization can
-- expose a missing field without guessing a set-membership witness.
theorem record_eq_keys (left right : List (String × Value))
    (h : record left = record right) :
    (∀ field ∈ left, string field.1 ∈ enumerate (right.map (fun f => string f.1))) ∧
    (∀ field ∈ right, string field.1 ∈ enumerate (left.map (fun f => string f.1))) := by
  have domains := congrArg domain h
  rw [domain_record, domain_record] at domains
  constructor
  · intro field member
    rw [← domains]
    exact (mem_enumerate _ _).mpr (List.mem_map.mpr ⟨field, member, rfl⟩)
  · intro field member
    rw [domains]
    exact (mem_enumerate _ _).mpr (List.mem_map.mpr ⟨field, member, rfl⟩)

theorem apply_record (fields : List (String × Value)) (key : String) (value : Value)
    (member : (key, value) ∈ fields)
    (unique : ∀ field ∈ fields, field.1 = key → field.2 = value) :
    apply (record fields) (string key) = value := by
  unfold record
  rw [apply_function]
  · obtain ⟨field, hf, hk, hv⟩ := choose_spec
      (fun v => ∃ field ∈ fields, string key = string field.1 ∧ v = field.2)
      ⟨value, (key, value), member, rfl, rfl⟩
    exact hv.trans (unique field hf (string_injective hk).symm)
  · apply (mem_enumerate _ _).mpr
    exact List.mem_map.mpr ⟨(key, value), member, rfl⟩

theorem record_as_pairs (fields : List (String × Value))
    (unique : ∀ a ∈ fields, ∀ b ∈ fields, a.1 = b.1 → a.2 = b.2) :
    record fields = enumerate (fields.map (fun f => ZFSet.pair (string f.1) f.2)) := by
  have selected (field : String × Value) (member : field ∈ fields) :
      choose (fun value => ∃ f ∈ fields, string field.1 = string f.1 ∧ value = f.2) = field.2 := by
    obtain ⟨f, hf, hk, hv⟩ := choose_spec
      (fun value => ∃ f ∈ fields, string field.1 = string f.1 ∧ value = f.2)
      ⟨field.2, field, member, rfl, rfl⟩
    exact hv.trans (unique f hf field member (string_injective hk).symm)
  apply ZFSet.ext
  intro p
  unfold record function
  simp only [mem_image, mem_enumerate]
  constructor
  · rintro ⟨key, hk, rfl⟩
    obtain ⟨field, hf, rfl⟩ := List.mem_map.mp hk
    rw [selected field hf]
    exact List.mem_map.mpr ⟨field, hf, rfl⟩
  · intro hp
    obtain ⟨field, hf, rfl⟩ := List.mem_map.mp hp
    refine ⟨string field.1, List.mem_map.mpr ⟨field, hf, rfl⟩, ?_⟩
    rw [selected field hf]

theorem enumerate_eq_iff (left right : List Value) :
    enumerate left = enumerate right ↔
      (∀ x ∈ left, x ∈ right) ∧ (∀ x ∈ right, x ∈ left) := by
  constructor
  · intro h
    constructor
    · intro x hx
      exact (mem_enumerate _ _).mp (h ▸ (mem_enumerate _ _).mpr hx)
    · intro x hx
      exact (mem_enumerate _ _).mp (h.symm ▸ (mem_enumerate _ _).mpr hx)
  · rintro ⟨forward, backward⟩
    apply ZFSet.ext
    intro x
    simpa only [mem_enumerate] using Iff.intro (forward x) (backward x)

theorem record_unique_of_nodup (fields : List (String × Value))
    (distinct : (fields.map Prod.fst).Nodup) :
    ∀ a ∈ fields, ∀ b ∈ fields, a.1 = b.1 → a.2 = b.2 := by
  induction fields with
  | nil => simp
  | cons head tail ih =>
    simp only [List.map_cons, List.nodup_cons] at distinct
    intro a ha b hb eq
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · rfl
      · exact False.elim (distinct.1 (List.mem_map.mpr ⟨b, hb, eq.symm⟩))
    · rcases hb with rfl | hb
      · exact False.elim (distinct.1 (List.mem_map.mpr ⟨a, ha, eq⟩))
      · exact ih distinct.2 a ha b hb eq

theorem apply_record_lookup (fields : List (String × Value)) (key : String)
    (distinct : (fields.map Prod.fst).Nodup) (member : key ∈ fields.map Prod.fst) :
    apply (record fields) (string key) = (fields.lookup key).getD undefined := by
  have present : (fields.lookup key).isSome := by
    obtain ⟨field, hf, hk⟩ := List.mem_map.mp member
    exact List.lookup_isSome_iff.mpr ⟨field, hf, by simp [hk]⟩
  cases found : fields.lookup key with
  | none => simp [found] at present
  | some value =>
    obtain ⟨before, after, decomposition, _⟩ := List.lookup_eq_some_iff.mp found
    have entry : (key, value) ∈ fields := by simp [decomposition]
    simp only [found, Option.getD_some]
    apply apply_record fields key value entry
    intro other ho eq
    exact record_unique_of_nodup fields distinct other ho (key, value) entry eq

theorem record_eq_iff (left right : List (String × Value))
    (hl : (left.map Prod.fst).Nodup)
    (hr : (right.map Prod.fst).Nodup) :
    record left = record right ↔
      (∀ p ∈ left.map (fun f => ZFSet.pair (string f.1) f.2),
        p ∈ right.map (fun f => ZFSet.pair (string f.1) f.2)) ∧
      (∀ p ∈ right.map (fun f => ZFSet.pair (string f.1) f.2),
        p ∈ left.map (fun f => ZFSet.pair (string f.1) f.2)) := by
  rw [record_as_pairs left (record_unique_of_nodup left hl),
    record_as_pairs right (record_unique_of_nodup right hr), enumerate_eq_iff]

theorem record_two_eq_iff (a b : String) (x y u v : Value) (different : a ≠ b) :
    record [(a, x), (b, y)] = record [(a, u), (b, v)] ↔ x = u ∧ y = v := by
  constructor
  · intro h
    have first := congrArg (fun f => apply f (string a)) h
    have second := congrArg (fun f => apply f (string b)) h
    have hba : (b == a) = false := beq_eq_false_iff_ne.mpr (Ne.symm different)
    simp [apply_record_lookup, different, Ne.symm different, List.lookup_cons, hba] at first second
    exact ⟨first, second⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem record_two_ne_iff (a b : String) (x y u v : Value) (different : a ≠ b) :
    record [(a, x), (b, y)] ≠ record [(a, u), (b, v)] ↔ x ≠ u ∨ y ≠ v := by
  rw [ne_eq, record_two_eq_iff a b x y u v different, not_and_or]

theorem powerset_subset_contradiction (domain range witness : Value)
    (included : ZFSet.powerset domain ⊆ range)
    (subset : witness ⊆ domain) (excluded : witness ∉ range) : False :=
  excluded (included (ZFSet.mem_powerset.mpr subset))

theorem separation_subset (s : Value) (p : Value → Prop) : s.sep p ⊆ s := by
  intro x hx
  exact (ZFSet.mem_sep.mp hx).1

theorem exists_nat_of_nonneg (z : Int) (h : 0 ≤ z) : ∃ n : Nat, (n : Int) = z :=
  ⟨z.toNat, Int.toNat_of_nonneg h⟩

theorem diagonal_ne (s f x : Value) (hx : x ∈ s) :
    apply f x ≠ s.sep (fun z => z ∉ apply f z) := by
  intro eq
  by_cases hm : x ∈ apply f x
  · have diagonal : x ∈ s.sep (fun z => z ∉ apply f z) := eq ▸ hm
    exact (ZFSet.mem_sep.mp diagonal).2 hm
  · have diagonal : x ∈ s.sep (fun z => z ∉ apply f z) :=
      ZFSet.mem_sep.mpr ⟨hx, hm⟩
    exact hm (eq.symm ▸ diagonal)

theorem exists_container (x : Value) : ∃ s : Value, x ∈ s :=
  ⟨enumerate [x], (mem_enumerate _ _).mpr (by simp)⟩

theorem prepend_tuple (x : Value) (values : List Value) :
    prepend x (tuple values) = tuple (x :: values) := by
  unfold prepend
  rw [length_tuple, toInt_integer]
  conv_rhs => unfold tuple
  simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
  apply function_congr
  intro key hkey
  obtain ⟨k, rfl⟩ := (mem_integers _).mp (ZFSet.mem_sep.mp hkey).1
  have bounds := (integer_mem_interval _ _ _).mp hkey
  simp only [toInt_integer]
  by_cases hk : k = 1
  · subst k
    simp
  · rw [if_neg hk, apply_tuple_at values (k - 1) (by omega)]
    have shift : (k - 1).toNat = (k - 2).toNat + 1 := by omega
    have subtract : k - 1 - 1 = k - 2 := by omega
    rw [subtract, shift, List.getElem?_cons_succ]

theorem mem_cartesian_cons (x first : Value) (rest : List Value) :
    x ∈ cartesian (first :: rest) ↔
      ∃ head ∈ first, ∃ tail ∈ cartesian rest, prepend head tail = x := by
  simp only [cartesian, ZFSet.mem_sUnion, mem_image]
  constructor
  · rintro ⟨_, ⟨head, hh, rfl⟩, member⟩
    obtain ⟨tail, ht, eq⟩ := (mem_image _ _ _).mp member
    exact ⟨head, hh, tail, ht, eq⟩
  · rintro ⟨head, hh, tail, ht, eq⟩
    exact ⟨image (cartesian rest) (prepend head), ⟨head, hh, rfl⟩,
      (mem_image _ _ _).mpr ⟨tail, ht, eq⟩⟩

theorem mem_cartesian_nil (x : Value) : x ∈ cartesian [] ↔ x = tuple [] := by
  simp [cartesian, mem_enumerate]

theorem mem_interval_iff (x : Value) (lo hi : Int) :
    x ∈ interval (integer lo) (integer hi) ↔
      ∃ n : Int, integer n = x ∧ lo ≤ n ∧ n ≤ hi := by
  constructor
  · intro hx
    obtain ⟨n, rfl⟩ := (mem_integers _).mp (ZFSet.mem_sep.mp hx).1
    exact ⟨n, rfl, (integer_mem_interval _ _ _).mp hx⟩
  · rintro ⟨n, rfl, h⟩
    exact (integer_mem_interval _ _ _).mpr h

theorem record_isFunc (fields : List (String × Value)) (range : Value)
    (hr : ∀ field ∈ fields, field.2 ∈ range) :
    ZFSet.IsFunc (enumerate (fields.map (fun field => string field.1))) range
      (record fields) := by
  unfold record
  apply function_isFunc
  intro key hk
  obtain ⟨field, hf, hkey⟩ := List.mem_map.mp ((mem_enumerate _ _).mp hk)
  obtain ⟨selected, hs, _, hv⟩ := choose_spec
    (fun value => ∃ field ∈ fields, key = string field.1 ∧ value = field.2)
    ⟨field.2, field, hf, hkey.symm, rfl⟩
  rw [hv]
  exact hr selected hs

theorem record_eta (fields : List (String × Value)) (f range : Value)
    (hf : ZFSet.IsFunc (enumerate (fields.map (fun field => string field.1))) range f)
    (values : ∀ field ∈ fields, apply f (string field.1) = field.2) :
    f = record fields := by
  have member (field : String × Value) (h : field ∈ fields) :
      string field.1 ∈ enumerate (fields.map (fun field => string field.1)) :=
    (mem_enumerate _ _).mpr (List.mem_map.mpr ⟨field, h, rfl⟩)
  have hr : ∀ field ∈ fields, field.2 ∈ range := by
    intro field h
    rw [← values field h]
    exact apply_mem hf (member field h)
  apply function_ext hf (record_isFunc fields range hr)
  intro key hk
  obtain ⟨field, h, rfl⟩ := List.mem_map.mp ((mem_enumerate _ _).mp hk)
  rw [values field h]
  symm
  apply apply_record fields field.1 field.2 h
  intro other ho eq
  rw [← values other ho, ← values field h, eq]

theorem mem_recordSpace (f : Value) (fields : List (String × Value)) :
    f ∈ recordSpace fields ↔
      ZFSet.IsFunc (enumerate (fields.map (fun field => string field.1)))
        (ZFSet.sUnion (enumerate (fields.map Prod.snd))) f ∧
      ∀ field ∈ fields, apply f (string field.1) ∈ field.2 := by
  simp only [recordSpace, ZFSet.mem_sep, ZFSet.mem_funs]

theorem diagonal_contradiction (s f x : Value) (hx : x ∈ s)
    (eq : apply f x = s.sep (fun z => z ∉ apply f z)) : False :=
  diagonal_ne s f x hx eq

theorem record_isFunc_of_domain (domain range : Value) (fields : List (String × Value))
    (hd : domain = enumerate (fields.map (fun field => string field.1)))
    (hr : ∀ field ∈ fields, field.2 ∈ range) :
    ZFSet.IsFunc domain range (record fields) := by
  subst domain
  exact record_isFunc fields range hr

theorem mem_union_enumerate (x : Value) (sets : List Value) :
    x ∈ ZFSet.sUnion (enumerate sets) ↔ ∃ s ∈ sets, x ∈ s := by
  simp only [ZFSet.mem_sUnion, mem_enumerate]

theorem mem_recordSpace_two (f A B : Value) (a b : String) (different : a ≠ b) :
    f ∈ recordSpace [(a, A), (b, B)] ↔
      ∃ x ∈ A, ∃ y ∈ B, f = record [(a, x), (b, y)] := by
  rw [mem_recordSpace]
  constructor
  · rintro ⟨hf, values⟩
    have ha : apply f (string a) ∈ A := values (a, A) (by simp)
    have hb : apply f (string b) ∈ B := values (b, B) (by simp)
    refine ⟨apply f (string a), ha, apply f (string b), hb, ?_⟩
    exact record_eta [(a, apply f (string a)), (b, apply f (string b))] f
      (ZFSet.sUnion (enumerate [A, B])) hf (by simp)
  · rintro ⟨x, hx, y, hy, rfl⟩
    constructor
    · exact record_isFunc [(a, x), (b, y)] (ZFSet.sUnion (enumerate [A, B]))
        (by simp [mem_enumerate, hx, hy])
    · have hba : (b == a) = false := beq_eq_false_iff_ne.mpr (Ne.symm different)
      simp [apply_record_lookup, different, Ne.symm different, List.lookup_cons, hba, hx, hy]

end TLAUniversal
