import Egg.Core.Request.Basic
import Egg.Core.Explanation.Proof
import Egg.Tactic.Config.Option
import Egg.Tactic.Config.Modifier
import Egg.Tactic.Base
import Egg.Tactic.Goal
import Egg.Tactic.Guides
import Egg.Tactic.Premises.Gen
import Egg.Tactic.Trace
import Egg.Tactic.Calcify
import Lean

open Lean Meta Elab Tactic

namespace Egg

-- TODO: We should also consider the level mvars of all `Fact`s.
private def collectAmbientMVars (goal : Goal) (guides : Guides) (proofErasure : Bool) :
    MetaM MVars.Ambient := do
  let expr ← MVars.Ambient.Expr.get
  let goalLvl := (← MVars.collect (← goal.expr) proofErasure).lvl
  let guidesLvl ← guides.foldlM (init := ∅) fun res g =>
    return res.merge (← MVars.collect g.expr proofErasure).lvl
  return { expr, lvl := goalLvl.merge guidesLvl }

private inductive Proof? where
  | proof (p : Expr)
  | retryWithShapes

private def resultToProof
    (result : Request.Result) (goal : Goal) (rws : Rewrites) (facts : Facts) (ctx : EncodingCtx)
    (retryWithShapes : Bool) : TacticM Proof? := do
  let proof ←
    try
      result.expl.proof rws facts result.egraph ctx
    catch err =>
      -- If proof reconstruction fails but we haven't tried using shapes yet, retry with shapes
      -- (assuming the correcspoding option is enabled).
      -- TODO: Using slotted e-graphs doesn't support shaped yet.
      if ctx.cfg.shapes || !retryWithShapes || ctx.cfg.slotted then
        throw err
      else
        return .retryWithShapes
  proof.trace `egg.proof
  let mut prf ← proof.prove goal.toCongr
  prf ← instantiateMVars prf
  withTraceNode `egg.proof.term (fun _ => return "Proof Term") do trace[egg.proof.term] prf
  catchLooseMVars prf ctx.amb proof.subgoals
  -- TODO: These mvars have the wrong depth.
  appendGoals proof.subgoals
  return .proof prf
where
  catchLooseMVars (prf : Expr) (amb : MVars.Ambient) (subgoals : List MVarId) : MetaM Unit := do
    let mvars ← MVars.collect prf (proofErasure := false)
    for mvar in mvars.expr do
      unless subgoals.contains mvar || amb.expr.contains mvar do
        throwError m!"egg: final proof contains expression mvar {Expr.mvar mvar}"
    for lmvar in mvars.lvl do
      unless amb.lvl.contains lmvar do
        throwError m!"egg: final proof contains level mvar {Level.mvar lmvar}"

open Config.Modifier (egg_cfg_mod)

protected partial def eval
    (mod : TSyntax ``egg_cfg_mod) (prems : TSyntax `egg_premises) (base : Option (TSyntax `egg_base))
    (guides : Option (TSyntax `egg_guides)) (basket? : Option Name := none)
    (calcifyTk? : Option Syntax := none) : TacticM Unit := do
  let save ← saveState
  try core catch err => restoreState save; throw err
where
  core : TacticM Unit := do
    let startTime ← IO.monoMsNow
    let goal ← getMainGoal
    let mod  ← Config.Modifier.parse mod
    let cfg := { (← Config.fromOptions).modify mod with basket? }
    cfg.trace `egg.config
    let goal ← Goal.gen goal base
    goal.id.withContext do
      let guides := (← guides.mapM Guides.parseGuides).getD #[]
      let amb ← collectAmbientMVars goal guides cfg.eraseProofs
      amb.trace `egg.ambient
      -- We increase the mvar context depth, so that ambient mvars aren't unified during proof
      -- reconstruction. Note that this also means that we can't assign the `goal` mvar here.
      let res ← withNewMCtxDepth do
        let (rws, facts) ← Premises.gen goal.toCongr prems guides cfg amb
        runEqSat goal rws facts guides cfg amb
      match res with
      | some (proof, proofTime, result, goalContainsBinder) =>
        if cfg.reporting then
          let totalTime := (← IO.monoMsNow) - startTime
          logInfo (s!"egg succeeded " ++ formatReport cfg.flattenReports result.report totalTime proofTime result.expl goalContainsBinder)
        goal.id.assignIfDefeq' proof
        if let some tk := calcifyTk? then calcify tk proof goal.intros
      | none => goal.id.admit
  runEqSat
      (goal : Goal) (rws : Rewrites) (facts : Facts) (guides : Guides) (cfg : Config)
      (amb : MVars.Ambient) : TacticM <| Option (Expr × Nat × Request.Result × Bool) := do
    let (req, goalContainsBinder) ← Request.encoding' goal.toCongr rws facts guides cfg amb
    withTraceNode `egg.encoded (fun _ => return "Encoded") do req.trace `egg.encoded
    if let .beforeEqSat := cfg.exitPoint then return none
    let result ← req.run cfg.explLengthLimit (onEqSatFailure cfg goalContainsBinder)
    result.expl.trace `egg.explanation.steps
    if let .beforeProof := cfg.exitPoint then return none
    let beforeProof ← IO.monoMsNow
    match ← resultToProof result goal rws facts {amb, cfg} cfg.retryWithShapes with
    | .proof prf =>
      let proofTime := (← IO.monoMsNow) - beforeProof
      return some (prf, proofTime, result, goalContainsBinder)
    | .retryWithShapes => runEqSat goal rws facts guides { cfg with shapes := true } amb
  onEqSatFailure (cfg : Config) (goalContainsBinder : Bool) (report : Request.Result.Report) :
      Request.Failure → MetaM MessageData
    | .backend => do
      let msg := s!"egg failed to prove the goal ({report.stopReason.description}) "
      unless cfg.reporting do return msg
      return msg ++ formatReport cfg.flattenReports report (goalContainsBinder := goalContainsBinder)
    | .explLength len => do
      let msg := s!"egg found an explanation exceeding the length limit ({len} vs {cfg.explLengthLimit})\nYou can increase this limit using 'set_option egg.explLengthLimit <num>'.\n"
      unless cfg.reporting do return msg
      return msg ++ formatReport cfg.flattenReports report (goalContainsBinder := goalContainsBinder)

syntax &"egg " egg_cfg_mod egg_premises (egg_base)? (egg_guides)? : tactic
elab_rules : tactic
  | `(tactic| egg $mod $prems $[$base]? $[$guides]?) => Egg.eval mod prems base guides

-- WORKAROUND: This fixes `Tests/EndOfInput *`.
macro "egg " mod:egg_cfg_mod : tactic => `(tactic| egg $mod)

-- The syntax `egg!` calls egg with the global egg basket.
elab "egg! " mod:egg_cfg_mod prems:egg_premises base:(egg_base)? guides:(egg_guides)? : tactic =>
  Egg.eval mod prems base guides (basket? := `egg)

-- WORKAROUND: This fixes a problem analogous to `Tests/EndOfInput *` for `egg!`.
macro "egg! " mod:egg_cfg_mod : tactic => `(tactic| egg! $mod)

-- The syntax `egg?` calls calcify after running egg.
elab tk:"egg? " mod:egg_cfg_mod prems:egg_premises base:(egg_base)? guides:(egg_guides)? : tactic =>
  Egg.eval mod prems base guides (basket? := none) (calcifyTk? := tk)

-- WORKAROUND: This fixes a problem analogous to `Tests/EndOfInput *` for `egg?`.
macro "egg? " mod:egg_cfg_mod : tactic => `(tactic| egg? $mod)
