/- Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license. -/
module
public import TLAUniversal.Values
public import TLAUniversal.InductionProofs
public import TLAUniversal.FunctionProofs
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

-- Avoid inventing a constant predicate to apply induction to unrelated goals.
elab "tla_natural_induction" : tactic => withMainContext do
  let goal ← getMainGoal
  let type ← whnf (← goal.getType)
  if type.isForall && type.bindingBody!.isForall then
    let bound := type.bindingBody!.bindingDomain!
    if bound.isAppOfArity ``Membership.mem 5 then
      let args := bound.getAppArgs
      if args[3]!.isConstOf ``TLAUniversal.naturals && args[4]! == mkBVar 0 then
        evalTactic (← `(tactic| refine TLAUniversal.natural_induction _ ?_ ?_))
        return
  throwError "expected a quantifier over TLA naturals"

/-- Elaborate a declaration only if Lean accepts it; otherwise leave the
environment unchanged. Used for optional Leibniz congruence lemmas whose
statements are true only for operators that evaluate their arguments in
the current state. A rejected attempt never adds a declaration. -/
elab "tla_try " cmd:command : command => do
  let saved ← get
  modify fun state => { state with messages := {} }
  Lean.Elab.Command.elabCommand (← `(command| set_option Elab.async false in $cmd))
  let after ← get
  if after.messages.hasErrors then
    set saved
  else
    set { after with messages := saved.messages }

/-- Instantiate bounded universal hypotheses `∀ x, x ∈ S → P x` with the
membership facts already in context (`t ∈ S`), as SMT trigger instantiation
does for TLAPS. Each instance is an application of existing hypotheses, so
nothing unproved is added. Fails when no new instance is found, which keeps
it usable as an aesop rule. -/
elab "tla_instantiate" : tactic => withMainContext do
  let goal ← getMainGoal
  let context ← getLCtx
  let mut seen : Array Expr := #[]
  for declaration in context do
    unless declaration.isImplementationDetail do
      seen := seen.push (← instantiateMVars declaration.type)
  let members := context.foldl (init := #[]) fun acc declaration =>
    if declaration.isImplementationDetail then acc else acc.push declaration
  let mut facts : Array (Expr × Expr) := #[]
  for declaration in context do
    if declaration.isImplementationDetail || facts.size ≥ 32 then continue
    let type ← instantiateMVars declaration.type
    unless type.isForall do continue
    for member in members do
      if facts.size ≥ 32 then break
      if member.fvarId == declaration.fvarId then continue
      let state ← saveState
      try
        let (arguments, _, body) ← forallMetaTelescopeReducing type (some 2)
        if arguments.size != 2 then
          state.restore
          continue
        if ← isDefEq (← inferType arguments[1]!) member.type then
          let term ← instantiateMVars (mkApp2 declaration.toExpr arguments[0]! member.toExpr)
          let termType ← instantiateMVars (← inferType term)
          let _ := body
          if !term.hasExprMVar && !termType.hasExprMVar && !seen.contains termType &&
              !(facts.any fun (_, t) => t == termType) then
            state.restore
            facts := facts.push (term, termType)
            continue
        state.restore
      catch _ =>
        state.restore
  if facts.isEmpty then
    throwError "no new bounded instance"
  let mut next := goal
  for (term, termType) in facts do
    let (_, updated) ← next.note `instance term (some termType)
    next := updated
  replaceMainGoal [next]

public theorem TLAUniversal.self_eq_succ_iff (n : Nat) : n = n + 1 ↔ False := iff_false_intro (Nat.succ_ne_self n).symm
public theorem TLAUniversal.succ_eq_self_iff (n : Nat) : n + 1 = n ↔ False := iff_false_intro (Nat.succ_ne_self n)

/-- Construct a witness for `∃ s : State, P s`, as ENABLED and `\cdot`
expansion need. Candidates are constant states built from `TRUE` and from
every value `v` with `truth v` in context. Each candidate is checked by closing the instantiated goal
(recursively for nested existentials); a candidate that does not close it is
discarded, so the result is an ordinary Lean proof. -/
meta partial def TLAUniversal.stateWitness (depth : Nat) : TacticM Unit := withMainContext do
  if depth == 0 then throwError "state witness depth exhausted"
  evalTactic (← `(tactic| try simp only [TLAUniversal.truth_boolean, if_true, if_false, ite_true, ite_false] at *))
  evalTactic (← `(tactic| intros))
  try evalTactic (← `(tactic| simp only [TLAUniversal.truth_boolean, TLAUniversal.tuple_eq_iff, List.cons.injEq, TLAUniversal.self_eq_succ_iff, TLAUniversal.succ_eq_self_iff, ZFSet.ZFBool.mem_𝔹_iff, TLAUniversal.boolean_eq_true_iff, TLAUniversal.boolean_eq_false_iff, if_true, if_false, ite_true, ite_false, and_true, true_and, eq_self_iff_true, ZFSet.zftrue_ne_zffalse, TLAUniversal.false_ne_true] at *))
  catch e => trace[debug] m!"norm error {e.toMessageData}"
  withMainContext do
  let goal ← getMainGoal
  let type ← whnfR (← instantiateMVars (← goal.getType))
  unless type.isAppOfArity ``Exists 2 do throwError "not an existential"
  let domain := type.appFn!.appArg!
  unless ← isDefEq domain (mkConst ``TLAUniversal.State) do
    throwError "not an existential over states"
  let predicate := type.appArg!
  let mut values : Array Expr := #[mkConst ``ZFSet.zftrue [levelZero]]
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    let t ← instantiateMVars declaration.type
    if t.isAppOfArity ``TLAUniversal.truth 1 && !t.appArg!.hasLooseBVars then
      unless values.contains t.appArg! do values := values.push t.appArg!
  values := values.push (mkConst ``ZFSet.zffalse [levelZero])
  -- Current states `b k` and variable names occurring in the goal give
  -- stuttering and single-variable-update candidates.
  let found ← IO.mkRef ((#[] : Array Expr), (#[] : Array String))
  type.forEach fun e => do
    match e with
    | .lit (.strVal name) => found.modify fun (xs, ns) => (xs, if ns.contains name then ns else ns.push name)
    | _ => pure ()
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    if ← isDefEq declaration.type (mkConst ``TLAUniversal.Behavior) then
      type.forEach fun e => do
        if e.isApp && e.appFn! == declaration.toExpr && !e.hasLooseBVars then
          found.modify fun (xs, ns) => (if xs.contains e then xs else xs.push e, ns)
  let (states, names) ← found.get
  let constant := values.map (fun v => Expr.lam `_ (mkConst ``String) v .default)
  let mut updates : Array Expr := #[]
  for state in states do
    updates := updates.push state
    for name in names do
      for value in values do
        if updates.size < 48 then
          let update ← withLocalDeclD `v (mkConst ``String) fun v => do
            let condition ← mkEq v (mkStrLit name)
            let body ← mkAppM ``ite #[condition, value, mkApp state v]
            mkLambdaFVars #[v] body
          updates := updates.push update
  -- Equation-driven candidates: from `s "v" = e` conjuncts in the goal,
  -- assign each variable its first required value, starting from each
  -- equation in turn so that every disjunct gets a chance.
  let equations ← withLocalDeclD `s (mkConst ``TLAUniversal.State) fun s => do
    let body := Expr.headBeta (mkApp predicate s)
    let collected ← IO.mkRef (#[] : Array (String × Expr))
    body.forEach fun e => do
      if e.isAppOfArity ``Eq 3 then
        let lhs := e.appFn!.appArg!
        let rhs := e.appArg!
        if lhs.isApp && lhs.appFn! == s then
          if let .lit (.strVal name) := lhs.appArg! then
            if !rhs.hasLooseBVars && !rhs.containsFVar s.fvarId! then
              collected.modify (·.push (name, rhs))
    collected.get
  let fallback : Expr → Expr := fun v =>
    match states[0]? with
    | some state => mkApp state v
    | none => mkConst ``ZFSet.zftrue [levelZero]
  let mut assigned : Array Expr := #[]
  for start in [0:equations.size] do
    if assigned.size ≥ 16 then break
    let mut chosen : Array (String × Expr) := #[]
    for offset in [0:equations.size] do
      let (name, value) := equations[(start + offset) % equations.size]!
      unless chosen.any (·.1 == name) do chosen := chosen.push (name, value)
    let candidate ← withLocalDeclD `v (mkConst ``String) fun v => do
      let mut body := fallback v
      for (name, value) in chosen.reverse do
        body ← mkAppM ``ite #[← mkEq v (mkStrLit name), value, body]
      mkLambdaFVars #[v] body
    assigned := assigned.push candidate
  -- States already in context (for example from a destructed ENABLED).
  let mut inContext : Array Expr := #[]
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    if ← isDefEq declaration.type (mkConst ``TLAUniversal.State) then
      inContext := inContext.push declaration.toExpr
  let candidates := inContext ++ constant ++ assigned ++ updates
  trace[debug] m!"state witness goal {type} equations {equations.size} candidates {candidates.size}"
  for candidate in candidates do
    let saved ← saveState
    try
      let proof ← mkFreshExprSyntheticOpaqueMVar (Expr.headBeta (mkApp predicate candidate))
      goal.assign (mkAppN (mkConst ``Exists.intro [← getLevel domain]) #[domain, predicate, candidate, proof])
      replaceMainGoal [proof.mvarId!]
      evalTactic (← `(tactic| try casesm* _ ∧ _))
      evalTactic (← `(tactic| first | (solve | simp_all [ZFSet.ZFBool.mem_𝔹_iff, TLAUniversal.truth_true, TLAUniversal.tuple_eq_iff, ZFSet.zftrue_ne_zffalse, TLAUniversal.false_ne_true, TLAUniversal.boolean_eq_true_iff, TLAUniversal.boolean_eq_false_iff, TLAUniversal.truth_boolean]) | simp_all [TLAUniversal.truth_true, TLAUniversal.tuple_eq_iff] | skip))
      if (← getUnsolvedGoals).isEmpty then return
      TLAUniversal.stateWitness (depth - 1)
      if (← getUnsolvedGoals).isEmpty then return
      saved.restore
    catch e =>
      saved.restore
      trace[debug] m!"state witness candidate failed: {e.toMessageData}"
  throwError "no state witness"

elab "tla_state_witness" : tactic => TLAUniversal.stateWitness 12
