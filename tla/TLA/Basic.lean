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
end TLA
