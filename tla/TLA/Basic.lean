/- Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license. -/
module

@[expose] public section
namespace TLA
universe u v
abbrev Behavior (σ : Type u) := Nat → σ
abbrev Predicate (σ : Type u) := σ → Prop
abbrev Action (σ : Type u) := σ → σ → Prop
abbrev Formula (σ : Type u) := Behavior σ → Nat → Prop

variable {σ : Type u} {α : Type v}

def state (p : Predicate σ) : Formula σ := fun b n => p (b n)
def action (a : Action σ) : Formula σ := fun b n => a (b n) (b (n + 1))
def always (p : Formula σ) : Formula σ := fun b n => ∀ m, n ≤ m → p b m
def eventually (p : Formula σ) : Formula σ := fun b n => ∃ m, n ≤ m ∧ p b m
def leadsTo (p q : Formula σ) : Formula σ :=
  always (fun b n => p b n → eventually q b n)
def enabled (a : Action σ) : Predicate σ := fun s => ∃ t, a s t
def unchanged (v : σ → α) : Action σ := fun s t => v t = v s
def square (a : Action σ) (v : σ → α) : Action σ :=
  fun s t => a s t ∨ unchanged v s t
def angle (a : Action σ) (v : σ → α) : Action σ :=
  fun s t => a s t ∧ ¬ unchanged v s t

def weakFairness (a : Action σ) (v : σ → α) : Formula σ := fun b n =>
  eventually (always (state (enabled (angle a v)))) b n →
  always (eventually (action (angle a v))) b n

def strongFairness (a : Action σ) (v : σ → α) : Formula σ := fun b n =>
  always (eventually (state (enabled (angle a v)))) b n →
  always (eventually (action (angle a v))) b n

def spec (init : Predicate σ) (next : Action σ) : Formula σ := fun b n =>
  init (b n) ∧ always (action (square next id)) b n

theorem invariant (init inv : Predicate σ) (next : Action σ)
    (initial : ∀ s, init s → inv s)
    (preserved : ∀ s t, inv s → next s t → inv t)
    (b : Behavior σ) (h : spec init next b 0) : always (state inv) b 0 := by
  intro n _
  induction n with
  | zero => exact initial _ h.1
  | succ n ih =>
    rcases h.2 n (Nat.zero_le n) with hn | hs
    · exact preserved _ _ (ih (Nat.zero_le n)) hn
    · change b (n + 1) = b n at hs
      change inv (b (n + 1))
      rw [hs]
      exact ih (Nat.zero_le n)

theorem always_now (p : Formula σ) (b : Behavior σ) (n : Nat)
    (h : always p b n) : p b n := h n (Nat.le_refl n)

theorem strong_implies_weak (a : Action σ) (v : σ → α)
    (b : Behavior σ) (n : Nat) (h : strongFairness a v b n) :
    weakFairness a v b n := by
  intro he
  apply h
  rcases he with ⟨k, _, hk⟩
  intro m hm
  exact ⟨max k m, Nat.le_max_right _ _, hk _ (Nat.le_max_left _ _)⟩
def compose (a b : Action σ) : Action σ := fun s t => ∃ mid, a s mid ∧ b mid t

/-- Repetition of states with no skipped state and no infinitely postponed suffix. -/
def expands (original expanded : Behavior σ) : Prop :=
  ∃ index : Nat → Nat, index 0 = 0 ∧
    (∀ n, index (n + 1) = index n ∨ index (n + 1) = index n + 1) ∧
    (∀ k, ∃ n, index n = k) ∧ ∀ n, expanded n = original (index n)

def stutteringEquivalent (left right : Behavior σ) : Prop :=
  ∃ common, expands left common ∧ expands right common

theorem expands_refl (b : Behavior σ) : expands b b := by
  exact ⟨id, rfl, fun _ => Or.inr rfl, fun k => ⟨k, rfl⟩, fun _ => rfl⟩

theorem stutteringEquivalent_refl (b : Behavior σ) : stutteringEquivalent b b :=
  ⟨b, expands_refl b, expands_refl b⟩

theorem stutteringEquivalent_head (b c : Behavior σ) (h : stutteringEquivalent b c) :
    b 0 = c 0 := by
  obtain ⟨common, ⟨i, hi, _, _, hbi⟩, ⟨j, hj, _, _, hcj⟩⟩ := h
  have left := hbi 0
  have right := hcj 0
  rw [hi] at left
  rw [hj] at right
  exact left.symm.trans right

/-- Flexible quantification closes existential hiding under finite stuttering. -/
def existsFlexible (p : (Nat → α) → Formula σ) : Formula σ := fun b n =>
  ∃ c, stutteringEquivalent (fun k => b (n + k)) c ∧ ∃ history, p history c 0

def forallFlexible (p : (Nat → α) → Formula σ) : Formula σ :=
  fun b n => ¬ existsFlexible (fun history c k => ¬ p history c k) b n

theorem existsFlexible_intro (p : (Nat → α) → Formula σ) (b : Behavior σ)
    (h : Nat → α) (hp : p h b 0) : existsFlexible p b 0 := by
  refine ⟨b, ?_, h, hp⟩
  simpa using stutteringEquivalent_refl b
/-- A finite prefix satisfies a property when it has a satisfying infinite extension. -/
def prefixSat (p : Formula σ) (b : Behavior σ) (n length : Nat) : Prop :=
  ∃ c : Behavior σ, (∀ i < length, c i = b (n + i)) ∧ p c 0

/-- TLA+'s guarantees operator, including the one-state-longer prefix condition. -/
def guarantees (p q : Formula σ) : Formula σ := fun b n =>
  (p b n → q b n) ∧ ∀ length, prefixSat p b n length → prefixSat q b n (length + 1)

theorem guarantees_implies (p q : Formula σ) (b : Behavior σ) (n : Nat)
    (h : guarantees p q b n) : p b n → q b n := h.1

theorem guarantees_true (p : Formula σ) (b : Behavior σ) (n : Nat) :
    guarantees p (fun _ _ => True) b n := by
  refine ⟨fun _ => trivial, ?_⟩
  intro length _
  exact ⟨fun i => b (n + i), by intros; rfl, trivial⟩
end TLA
