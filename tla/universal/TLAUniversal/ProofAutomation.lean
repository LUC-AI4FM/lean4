/- Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license. -/
module
public import TLAUniversal.Values
public import Lean

open Lean Meta Elab Tactic
open TLAUniversal

public theorem TLAUniversal.choose_case (p : Value → Prop) :
    p (choose p) ∨ ¬ ∃ x, p x := by
  classical
  by_cases h : ∃ x, p x
  · exact Or.inl (choose_spec p h)
  · exact Or.inr h

-- Keep a marker that normalization cannot erase when simplifying choose_case.
@[irreducible] public def TLAUniversal.choiceProcessed (_p : Value → Prop) : Prop := True

public theorem TLAUniversal.choice_processed (p : Value → Prop) : choiceProcessed p := by
  unfold choiceProcessed
  trivial

elab "tla_choice" : tactic => withMainContext do
  let goal ← getMainGoal
  let context ← getLCtx
  let mut expressions := #[(← goal.getType)]
  for declaration in context do
    expressions := expressions.push declaration.type
  let candidates ← IO.mkRef (#[] : Array Expr)
  for expression in expressions do
    expression.forEach fun e => do
      if e.isAppOfArity ``TLAUniversal.choose 1 && !e.hasLooseBVars && !e.hasExprMVar then
        candidates.modify (·.push e.appArg!)
  for predicate in (← candidates.get) do
    let proof ← mkAppM ``TLAUniversal.choose_case #[predicate]
    let _ ← inferType proof
    let mut present := false
    for declaration in context do
      if declaration.type.isAppOfArity ``TLAUniversal.choiceProcessed 1 &&
          declaration.type.appArg! == predicate then present := true
    if !present then
      let (_, next) ← goal.note `choice_fact proof
      let marker ← mkAppM ``TLAUniversal.choice_processed #[predicate]
      let (_, next) ← next.note `choice_processed marker
      replaceMainGoal [next]
      return
  throwError "no unprocessed choice expression"

public theorem TLAUniversal.temporal_induction (p : Nat → Prop) (start : Nat)
    (base : p start) (step : ∀ k, start ≤ k → p k → p (k + 1)) :
    ∀ k, start ≤ k → p k := by
  intro k hk
  obtain ⟨distance, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction distance with
  | zero => simpa using base
  | succ distance ih =>
    exact step (start + distance) (by omega) ih

-- Only apply induction to a future-time quantifier. Introducing preceding
-- premises does not turn those premises into globally valid temporal facts.
elab "tla_temporal_induction" : tactic => do
  for _ in [:16] do
    let goal ← getMainGoal
    let type ← withMainContext <| whnf (← goal.getType)
    if type.isForall then
      let body := type.bindingBody!
      if type.bindingDomain!.isConstOf ``Nat && body.isForall then
        let bound := body.bindingDomain!
        if (bound.isAppOfArity ``LE.le 4 || bound.isAppOfArity ``Nat.le 2) &&
            bound.getAppArgs.back! == mkBVar 0 then
          evalTactic (← `(tactic| refine TLAUniversal.temporal_induction _ _ ?_ ?_))
          return
      evalTactic (← `(tactic| intro))
    else
      throwError "expected a future-time quantifier"
  throwError "too many premises before the future-time quantifier"
