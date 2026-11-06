/- Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license. -/
module
public import TLAUniversal.Values
public import TLAUniversal.InductionProofs
public import TLAUniversal.FunctionProofs
public import TLAUniversal.Temporal
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

/-! ### Fairness-driven liveness (`BY PTL` leaves)

`tla_wf_rank [defs]` proves an eventuality `∃ k, n ≤ k ∧ Q k` from a weak or
strong fairness hypothesis by the checked rule `TLAUniversal.PTL.wf_rank`.
It only chooses the rank predicate `P` (constant `True`, or a state predicate
that a cited step fact establishes in the next state) and the starting time
(the goal's time, or the time of an eventuality hypothesis). Each premise of
the rule is then a single-time obligation that ordinary search must prove;
a choice whose premises fail is discarded. -/

/-- `∃ k, n ≤ k ∧ Q k` as `(n, fun k => Q k)`. -/
meta def TLAUniversal.matchEventually (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``Exists 2 then
    match e.appArg! with
    | .lam name ty body bi =>
      if ty.isConstOf ``Nat && body.isAppOfArity ``And 2 then
        let le := body.appFn!.appArg!
        if le.isAppOfArity ``LE.le 4 && le.appArg! == .bvar 0 && !le.appFn!.appArg!.hasLooseBVars then
          some (le.appFn!.appArg!, .lam name ty body.appArg! bi)
        else none
      else none
    | _ => none
  else none

meta def TLAUniversal.isBehavior (e : Expr) : MetaM Bool :=
  withNewMCtxDepth <| withReducible <| isDefEq e (mkConst ``TLAUniversal.Behavior)

/-- Is `type` of the form `∀ (b : Behavior) (n : Nat), _`? -/
meta def TLAUniversal.isGeneralFact (type : Expr) : MetaM Bool := do
  match type with
  | .forallE _ d (.forallE _ d' _ _) _ =>
    return d'.isConstOf ``Nat && (← TLAUniversal.isBehavior d)
  | _ => return false

/-- Is `type` of the form `∀ m : Nat, lo ≤ m → _`? Returns `lo`. -/
meta def TLAUniversal.futureBound (type : Expr) : Option Expr :=
  match type with
  | .forallE _ d (.forallE _ le _ _) _ =>
    if d.isConstOf ``Nat && le.isAppOfArity ``LE.le 4 && le.appArg! == .bvar 0 &&
        !le.appFn!.appArg!.hasLooseBVars then some le.appFn!.appArg! else none
  | _ => none

/-- Prove `lo ≤ k` by omega in the current context. -/
meta def TLAUniversal.proveLe (lo k : Expr) : TacticM (Option Expr) := do
  let proof ← mkFreshExprMVar (← mkAppM ``LE.le #[lo, k])
  let saved ← saveState
  try
    let remaining ← Tactic.run proof.mvarId! (evalTactic (← `(tactic| omega)))
    if remaining.isEmpty then return some (← instantiateMVars proof)
    saved.restore; return none
  catch _ =>
    saved.restore; return none

/-- Instantiate time-universal facts at the current behavior and time `k`
(and `k + 1`), then clear the universal forms. Every added fact is an
application of an existing hypothesis. -/
meta def TLAUniversal.isTemporal (e : Expr) : Bool :=
  (e.find? fun x => x.isAppOf ``TLA.weakFairness || x.isAppOf ``TLA.strongFairness ||
    (x.isForall && x.bindingDomain!.isConstOf ``Nat)).isSome

meta def TLAUniversal.instantiateAt (behavior k : Expr) (both : Bool := false) : TacticM Unit := withMainContext do
  let mut goal ← getMainGoal
  let mut cleared : Array FVarId := #[]
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    let type ← instantiateMVars declaration.type
    let times ← if both then pure #[k, ← mkAppM ``HAdd.hAdd #[k, mkNatLit 1]] else pure #[k]
    if ← TLAUniversal.isGeneralFact type then
      for time in times do
        let term := mkApp2 declaration.toExpr behavior time
        let termType := (← instantiateMVars (← inferType term)).headBeta
        -- A fact whose premise is itself temporal cannot be discharged at a
        -- single time; it only slows the search.
        unless termType.isArrow && TLAUniversal.isTemporal termType.bindingDomain! do
          let (_, g) ← goal.note declaration.userName term
          goal := g
      cleared := cleared.push declaration.fvarId
    else if let some lo := TLAUniversal.futureBound type then
      for time in times do
        replaceMainGoal [goal]
        if let some le ← withMainContext (TLAUniversal.proveLe lo time) then
          let (_, g) ← goal.note declaration.userName (mkApp2 declaration.toExpr time le)
          goal := g
      cleared := cleared.push declaration.fvarId
    else if TLAUniversal.isTemporal type then
      cleared := cleared.push declaration.fvarId
  goal ← goal.tryClearMany cleared
  replaceMainGoal [goal]

/-- Run `tactic` on the main goal with its own heartbeat budget (in
thousands of `maxHeartbeats` units); succeed only if it closes the goal. Any failure, including a
resource limit, restores the state and returns `false`. -/
meta def TLAUniversal.closes (budget : Nat) (tactic : TacticM Unit) : TacticM Bool := do
  let saved ← saveState
  let goals ← getGoals
  let main ← getMainGoal
  tryCatchRuntimeEx
    (do
      setGoals [main]
      let start ← IO.getNumHeartbeats
      withTheReader Core.Context
        (fun ctx => { ctx with initHeartbeats := start, maxHeartbeats := budget * 1000 * 1000 }) tactic
      if (← getUnsolvedGoals).isEmpty then
        setGoals goals.tail
        return true
      saved.restore
      return false)
    (fun e => do
      trace[debug] m!"closes failed: {e.toMessageData}"
      saved.restore
      return false)

/-- Replace every `truth e` in the goal and hypotheses by a propositional
variable (TLAPS's atom abstraction). Generalizing only weakens the goal. -/
meta def TLAUniversal.abstractAtoms : TacticM Unit := withMainContext do
  let atoms ← IO.mkRef (#[] : Array Expr)
  let visit (e : Expr) : TacticM Unit := do
    e.forEach fun x => do
      let valueEq := x.isAppOfArity ``Eq 3 &&
        ((x.getArg! 0).isConstOf ``TLAUniversal.Value || (x.getArg! 0).isAppOf ``ZFSet)
      if (x.isAppOfArity ``TLAUniversal.truth 1 || valueEq) && !x.hasLooseBVars && !x.hasMVar then
        atoms.modify fun xs => if xs.contains x then xs else xs.push x
  visit (← instantiateMVars (← (← getMainGoal).getType))
  for declaration in ← getLCtx do
    unless declaration.isImplementationDetail do visit (← instantiateMVars declaration.type)
  for atom in ← atoms.get do
    let a ← Term.exprToSyntax atom
    evalTactic (← `(tactic| generalize $a:term = atom at *))

/-- Close a single-time obligation at time `k`: instantiate the
time-universal facts there, try the cited facts as atoms (as TLAPS's PTL
does), then with every definition unfolded. -/
meta def TLAUniversal.closeAt (behavior k : Expr) (unfold : Array Ident) (both : Bool := false) : TacticM Unit := do
  TLAUniversal.instantiateAt behavior k both
  evalTactic (← `(tactic| intros))
  let mut lemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
  for i in unfold ++ #[mkIdent ``TLAUniversal.truth_boolean, mkIdent ``TLA.enabled, mkIdent ``TLA.angle,
      mkIdent ``TLA.unchanged, mkIdent ``TLA.square] do
    lemmas := lemmas.push (← `(Lean.Parser.Tactic.simpLemma| $i:ident))
  if ← TLAUniversal.closes 20 (withReducible do TLAUniversal.abstractAtoms; evalTactic (← `(tactic| simp_all))) then return
  if ← TLAUniversal.closes 20 (withReducible do TLAUniversal.abstractAtoms; evalTactic (← `(tactic| tauto))) then return
  if ← TLAUniversal.closes 200 (evalTactic (← `(tactic| (try simp only [$lemmas,*] at *); intros; simp_all))) then return
  trace[debug] m!"single-time obligation not proved: {← getMainGoal}"
  throwError "single-time obligation not proved"

/-- Close one single-time premise of `wf_rank`. -/
meta def TLAUniversal.closeRankPremise (behavior : Expr) (unfold : Array Ident) : TacticM Unit := do
  let goal ← getMainGoal
  let (fvars, goal) ← goal.introNP 2
  replaceMainGoal [goal]
  TLAUniversal.closeAt behavior (mkFVar fvars[0]!) unfold

/-- A proof of `premise` from hypotheses, splitting conjunctions. -/
meta partial def TLAUniversal.findProof (context : LocalContext) (premise : Expr) : MetaM (Option Expr) := do
  for other in context do
    if other.isImplementationDetail then continue
    if ← withNewMCtxDepth (withReducible (isDefEq other.type premise)) then
      return some other.toExpr
  if premise.isAppOfArity ``And 2 then
    if let some a ← TLAUniversal.findProof context premise.appFn!.appArg! then
      if let some b ← TLAUniversal.findProof context premise.appArg! then
        return some (mkApp4 (mkConst ``And.intro) premise.appFn!.appArg! premise.appArg! a b)
  return none

/-- Instantiate the general facts at the goal's own time and discharge their
antecedents with hypotheses already in context. -/
meta def TLAUniversal.currentFacts (behavior time : Expr) : TacticM Unit := withMainContext do
  let mut goal ← getMainGoal
  let context ← getLCtx
  for declaration in context do
    if declaration.isImplementationDetail then continue
    let type ← instantiateMVars declaration.type
    unless ← TLAUniversal.isGeneralFact type do continue
    let mut term := mkApp2 declaration.toExpr behavior time
    let mut termType := (← instantiateMVars (← inferType term)).headBeta
    let mut applied := false
    while termType.isArrow do
      match ← TLAUniversal.findProof context termType.bindingDomain! with
      | some proof =>
        term := mkApp term proof
        termType := termType.bindingBody!
        applied := true
      | none => break
    if applied then
      let (_, g) ← goal.note declaration.userName term
      goal := g
  replaceMainGoal [goal]

/-- Rank candidates: state predicates that a general fact concludes about
the next state, abstracted over time and placed on the current behavior. -/
meta def TLAUniversal.rankCandidates (behavior : Expr) : TacticM (Array Expr) := withMainContext do
  let mut result : Array Expr := #[]
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    let type ← instantiateMVars declaration.type
    unless ← TLAUniversal.isGeneralFact type do continue
    let found ← forallBoundedTelescope type (some 2) fun xs body => do
      let b0 := xs[0]!
      let n0 := xs[1]!
      let mut conclusion := body
      while conclusion.isArrow do conclusion := conclusion.bindingBody!
      let mut parts : Array Expr := #[conclusion]
      let mut atoms : Array Expr := #[]
      while !parts.isEmpty do
        let part := parts.back!
        parts := parts.pop
        if part.isAppOfArity ``Or 2 || part.isAppOfArity ``And 2 then
          parts := parts.push part.appFn!.appArg! |>.push part.appArg!
        else
          atoms := atoms.push part
      let next ← mkAppM ``HAdd.hAdd #[n0, mkNatLit 1]
      let mut out : Array Expr := #[]
      for atom in atoms do
        if atom.hasLooseBVars then continue
        -- Replace the behavior before abstracting: `replaceFVar` would
        -- otherwise also instantiate the abstracted time variable.
        let placed := atom.replaceFVar b0 behavior
        let abstracted ← kabstract placed next
        if !abstracted.hasLooseBVars || abstracted.containsFVar n0.fvarId! then continue
        out := out.push (Expr.lam `k (mkConst ``Nat) abstracted .default)
      return out
    for candidate in found do
      unless result.contains candidate do result := result.push candidate
  return result

meta def TLAUniversal.wfRank (unfold : Array Ident) : TacticM Unit := withMainContext do
  evalTactic (← `(tactic| intros))
  evalTactic (← `(tactic| try simp only [TLAUniversal.truth_boolean] at *))
  withMainContext do
  -- Locate fairness and the main behavior before splitting the context.
  let mut fairness : Option (Expr × Expr × Bool) := none
  for _ in [0:2] do
    fairness ← withMainContext do
      let mut found := none
      for declaration in ← getLCtx do
        if declaration.isImplementationDetail then continue
        let type ← instantiateMVars declaration.type
        if type.isAppOfArity ``TLA.weakFairness 6 then
          found := some (type, declaration.toExpr, true)
        else if type.isAppOfArity ``TLA.strongFairness 6 then
          found := some (type, declaration.toExpr, false)
      return found
    if fairness.isSome then break
    evalTactic (← `(tactic| try casesm* _ ∧ _))
  let some (fairType, _, _) := fairness | throwError "no fairness hypothesis"
  let args := fairType.getAppArgs
  let behavior := args[4]!
  let some (time, _) := TLAUniversal.matchEventually (← instantiateMVars (← (← getMainGoal).getType)).cleanupAnnotations
    | throwError "goal is not an eventuality"
  TLAUniversal.currentFacts behavior time
  evalTactic (← `(tactic| try casesm* _ ∧ _))
  withMainContext do
  let candidates := #[Expr.lam `k (mkConst ``Nat) (mkConst ``True) .default] ++ (← TLAUniversal.rankCandidates behavior)
  -- Starting times: the goal's time, then each eventuality hypothesis.
  let mut eventualities : Array FVarId := #[]
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    if (TLAUniversal.matchEventually (← instantiateMVars declaration.type)).isSome then
      eventualities := eventualities.push declaration.fvarId
  let attempt (start : Option FVarId) (rank : Expr) : TacticM Unit := withMainContext do
    let mut fair : Option Expr := none
    for declaration in ← getLCtx do
      if declaration.isImplementationDetail then continue
      let type ← instantiateMVars declaration.type
      if type.isAppOfArity ``TLA.weakFairness 6 then
        let a := type.getAppArgs
        fair := some (← mkAppM ``TLAUniversal.PTL.weakFairness_fair #[a[2]!, a[3]!, a[4]!, a[5]!, declaration.toExpr])
      else if type.isAppOfArity ``TLA.strongFairness 6 && fair.isNone then
        let a := type.getAppArgs
        fair := some (← mkAppM ``TLAUniversal.PTL.strongFairness_fair #[a[2]!, a[3]!, a[4]!, a[5]!, declaration.toExpr])
    let some fairProof := fair | throwError "no fairness hypothesis"
    let fairStx ← Term.exprToSyntax fairProof
    let rankStx ← Term.exprToSyntax rank
    match start with
    | none =>
      evalTactic (← `(tactic| refine TLAUniversal.PTL.wf_rank _ _ $rankStx _ _ _ $fairStx (Nat.le_refl _) ?_ ?_ ?_ ?_))
    | some h =>
      let hStx ← Term.exprToSyntax (mkFVar h)
      evalTactic (← `(tactic| refine TLAUniversal.PTL.eventually_from _ _ _ $hStx ?_))
      evalTactic (← `(tactic| intro start start_le start_holds))
      evalTactic (← `(tactic| refine TLAUniversal.PTL.wf_rank _ _ $rankStx _ _ start $fairStx (by omega) ?_ ?_ ?_ ?_))
    let goals ← getGoals
    trace[debug] m!"rank {rank} premises {goals.length}"
    for g in goals do
      setGoals [g]
      TLAUniversal.closeRankPremise behavior unfold
    unless (← getUnsolvedGoals).isEmpty do throwError "premises remain"
  for start in #[none] ++ eventualities.map some do
    for rank in candidates do
      let saved ← saveState
      try
        attempt start rank
        return
      catch e =>
        trace[debug] m!"wf_rank attempt failed: {e.toMessageData} {e.isInterrupt} {e.isRuntime}"
        saved.restore
  throwError "no fairness rank closes the goal"

syntax (name := tlaWfRank) "tla_wf_rank" " [" ident,* "]" : tactic
elab_rules : tactic
  | `(tactic| tla_wf_rank [$ids,*]) =>
    tryCatchRuntimeEx (TLAUniversal.wfRank ids.getElems) fun _ => throwError "tla_wf_rank: resource limit"


/-- The last behavior variable in context (the one the goal is about). -/
meta def TLAUniversal.currentBehavior : TacticM Expr := withMainContext do
  let mut found := none
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    if ← TLAUniversal.isBehavior declaration.type then found := some declaration.toExpr
  match found with
  | some b => return b
  | none => throwError "no behavior in context"

/-- `tla_ptl_invariant [defs]` proves `∀ m, n ≤ m → I m` by
`TLAUniversal.temporal_induction`; the base case and the step are
single-time obligations over the instantiated facts. -/
meta def TLAUniversal.introPremises : TacticM Unit := do
  for _ in [0:64] do
    let goal ← getMainGoal
    let type := (← instantiateMVars (← goal.getType)).cleanupAnnotations
    unless type.isArrow do return
    let (_, g) ← goal.intro1
    replaceMainGoal [g]

meta def TLAUniversal.ptlInvariant (unfold : Array Ident) : TacticM Unit := do
  evalTactic (← `(tactic| try simp only [TLAUniversal.truth_boolean]))
  TLAUniversal.introPremises
  evalTactic (← `(tactic| try simp only [TLAUniversal.truth_boolean] at *))
  evalTactic (← `(tactic| try casesm* _ ∧ _))
  let behavior ← TLAUniversal.currentBehavior
  let some time := TLAUniversal.futureBound (← instantiateMVars (← (← getMainGoal).getType)).cleanupAnnotations
    | throwError "goal is not an invariant"
  withMainContext (TLAUniversal.currentFacts behavior time)
  evalTactic (← `(tactic| try casesm* _ ∧ _))
  -- Pointwise first: `[]P` from facts that already hold at every time.
  let pointwise ← TLAUniversal.closes 400 do
    let (fvars, g) ← (← getMainGoal).introNP 2
    replaceMainGoal [g]
    TLAUniversal.closeAt behavior (mkFVar fvars[0]!) unfold
  if pointwise then return
  evalTactic (← `(tactic| refine TLAUniversal.temporal_induction _ _ ?_ ?_))
  let goals ← getGoals
  let some base := goals[0]? | throwError "induction failed"
  let some step := goals[1]? | throwError "induction failed"
  setGoals [base]
  TLAUniversal.closeAt behavior time unfold
  setGoals [step]
  let (fvars, g) ← step.introNP 2
  replaceMainGoal [g]
  TLAUniversal.closeAt behavior (mkFVar fvars[0]!) unfold

syntax (name := tlaPtlInvariant) "tla_ptl_invariant" " [" ident,* "]" : tactic
elab_rules : tactic
  | `(tactic| tla_ptl_invariant [$ids,*]) =>
    tryCatchRuntimeEx (TLAUniversal.ptlInvariant ids.getElems) fun _ => throwError "tla_ptl_invariant: resource limit"

/-- Prove `z ∈ domain f` from `z ∈ D` and `f ∈ [D -> E]` in context. -/
macro "tla_domain" : tactic =>
  `(tactic| first
    | assumption
    | (rw [TLAUniversal.domain_of_mem_funs (by assumption)]; assumption)
    | (rw [TLAUniversal.domain_isFunc (by assumption)]; assumption))

/-- Read EXCEPT updates at arguments known to lie in the function's domain
(`[f EXCEPT ![x] = v][z] = IF z = x THEN v ELSE f[z]`). Fails without progress. -/
macro "tla_except" : tactic =>
  `(tactic| simp (disch := tla_domain) only [TLAUniversal.apply_update_eq] at *)

/-- Close one case of an EXCEPT step: read updates as conditionals, split
them, then finish by simplification with bounded instantiation. -/
macro "tla_except_close" : tactic =>
  `(tactic| (
    intros
    try simp only [TLAUniversal.updatePath] at ⊢
    try tla_except
    try split_ifs
    all_goals first
      | (solve | simp_all)
      | (solve | (repeat tla_instantiate); simp_all)
      | (solve | apply TLAUniversal.update_isFunc <;> first | assumption | simp_all)
      | (solve | apply TLAUniversal.updatePath_single_mem_funs <;> first | assumption | simp_all)
      | (solve | aesop (config := { maxRuleApplications := 200, terminal := true }) (add safe (by tla_instantiate)))))

/-- Rewrite the goal with the next-state equations `b (n + 1) "v" = e` in context. -/
meta def TLAUniversal.rewriteNextState : TacticM Unit := withMainContext do
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    let type := (← instantiateMVars declaration.type).cleanupAnnotations
    let some (_, lhs, rhs) := type.eq? | continue
    unless lhs.getAppNumArgs == 2 && lhs.getAppFn.isFVar do continue
    unless lhs.appArg!.isStringLit do continue
    unless lhs.appFn!.appArg!.isAppOfArity ``HAdd.hAdd 6 do continue
    if rhs.containsFVar lhs.getAppFn.fvarId! && (rhs.find? (· == lhs)).isSome then continue
    let h ← Term.exprToSyntax declaration.toExpr
    evalTactic (← `(tactic| try rw [$h:term]))

/-- `tla_except_step`: an invariant step whose next state is given by
EXCEPT updates. Splits the hypotheses into cases, substitutes the next
state, and reads every update as a conditional (`TLAUniversal.apply_update_eq`).
Each case is an ordinary Lean proof; a case that fails makes the tactic fail. -/
meta def TLAUniversal.exceptStep : TacticM Unit := do
  let goal ← getMainGoal
  let mentions (e : Expr) := (e.find? fun x => x.isAppOf ``TLAUniversal.update || x.isAppOf ``TLAUniversal.updatePath).isSome
  let mut found := mentions (← instantiateMVars (← goal.getType))
  for declaration in ← goal.withContext getLCtx do
    found := found || mentions (← instantiateMVars declaration.type)
  unless found do throwError "no EXCEPT update"
  evalTactic (← `(tactic| intros))
  evalTactic (← `(tactic| try casesm* _ ∧ _, _ ∨ _, ∃ _, _))
  let goals ← getGoals
  let mut remaining := #[]
  for g in goals do
    setGoals [g]
    TLAUniversal.rewriteNextState
    evalTactic (← `(tactic| repeat' apply And.intro))
    remaining := remaining ++ (← getGoals)
  for g in remaining do
    setGoals [g]
    unless ← TLAUniversal.closes 100 (evalTactic (← `(tactic| tla_except_close))) do
      throwError "EXCEPT step case not proved"
  setGoals []

syntax (name := tlaExceptStep) "tla_except_step" : tactic
elab_rules : tactic
  | `(tactic| tla_except_step) =>
    tryCatchRuntimeEx TLAUniversal.exceptStep fun _ => throwError "tla_except_step: resource limit"

/-- Run a tactic, turning a resource exception (recursion depth, heartbeats)
into an ordinary failure so that an enclosing `first` can try its next
alternative. It never turns a failure into success. -/
syntax (name := tlaGuard) "tla_guard " tacticSeq : tactic
elab_rules : tactic
  | `(tactic| tla_guard $t) =>
    tryCatchRuntimeEx (evalTactic t) fun e => throwError "tla_guard: {e.toMessageData}"
