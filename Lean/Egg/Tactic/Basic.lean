import Egg.Core.Request.Basic
import Egg.Core.Explanation.Proof
import Egg.Tactic.Config.Option
import Egg.Tactic.Config.Modifier
import Egg.Tactic.Goal
import Egg.Tactic.Guides
import Egg.Tactic.Premises.Gen.Basic
import Egg.Core.Gen.Guides
import Egg.Tactic.Trace
import Egg.Tactic.Calcify
import Lean

open Lean Meta Elab Tactic

namespace Egg

private inductive Proof? where
  | proof (p : Expr)
  | retryWithShapes

private def resultToProof
    (result : Request.Result) (goal : Goal) (rws : Rewrites) (ctx : EncodingCtx)
    (retryWithShapes : Bool) (proofFuel? : Option Nat) : TacticM Proof? := do
  let mut (proof, steps) ←
    try
      result.expl.prove' goal.toCongr rws result.egraph ctx proofFuel?
    catch err =>
      -- If proof reconstruction fails but we haven't tried using shapes yet, retry with shapes
      -- (assuming the correcspoding option is enabled).
      -- TODO: Using slotted e-graphs doesn't support shaped yet.
      if ctx.cfg.shapes || !retryWithShapes || ctx.cfg.slotted then
        throw err
      else
        return .retryWithShapes
  steps.trace `egg.proof
  proof ← instantiateMVars proof
  withTraceNode `egg.proof.term (fun _ => return "Proof Term") do trace[egg.proof.term] proof
  catchLooseMVars proof ctx.amb steps.subgoals
  -- TODO: These mvars have the wrong depth.
  appendGoals steps.subgoals
  return .proof proof
where
  catchLooseMVars (prf : Expr) (amb : MVars.Ambient) (subgoals : List MVarId) : MetaM Unit := do
    let mvars ← MVars.collect prf ∅
    for mvar in mvars.visibleExpr .noErase do
      unless subgoals.contains mvar || amb.expr.contains mvar do
        throwError m!"egg: final proof contains expression mvar {Expr.mvar mvar}"
    for lmvar in mvars.visibleLevel .noErase do
      unless amb.lvl.contains lmvar do
        throwError m!"egg: final proof contains level mvar {Level.mvar lmvar}"

open Config.Modifier (egg_cfg_mod)

protected partial def eval
    (mod : TSyntax ``egg_cfg_mod) (prems : TSyntax `egg_premises)
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
    let goal ← Goal.gen goal
    goal.id.withContext do
      let guides := (← guides.mapM Guides.parseGuides).getD #[]
      let amb ← MVars.Ambient.collect
      amb.trace `egg.ambient
      -- We increase the mvar context depth, so that ambient mvars aren't unified during proof
      -- reconstruction. Note that this also means that we can't assign the `goal` mvar here.
      let res ← withNewMCtxDepth do
        let rws ← Premises.gen goal prems guides cfg amb
        let guides ← do if cfg.derivedGuides then pure (guides ++ (← genDerivedGuides goal.toCongr rws amb)) else pure guides
        runEqSat goal rws guides cfg amb
      match res with
      | some (proof, proofTime, result, goalContainsBinder) =>
        if cfg.reporting then
          let totalTime := (← IO.monoMsNow) - startTime
          logInfo (s!"egg succeeded " ++ formatReport cfg.flattenReports result.report totalTime proofTime result.expl goalContainsBinder)
        goal.id.assignIfDefeq' proof
        if let some tk := calcifyTk? then calcify tk proof goal.intros.unzip.snd
      | none => goal.id.admit
  runEqSat
      (goal : Goal) (rws : Rewrites) (guides : Guides) (cfg : Config) (amb : MVars.Ambient) :
      TacticM <| Option (Expr × Nat × Request.Result × Bool) := do
    let (req, goalContainsBinder) ← Request.encoding' goal.toCongr rws guides cfg amb
    withTraceNode `egg.encoded (fun _ => return "Encoded") do req.trace `egg.encoded
    if let .beforeEqSat := cfg.exitPoint then return none
    let result ← req.run cfg.explLengthLimit (onEqSatFailure cfg goalContainsBinder)
    result.expl.trace `egg.explanation.steps
    if let .beforeProof := cfg.exitPoint then return none
    let beforeProof ← IO.monoMsNow
    match ← resultToProof result goal rws {amb, cfg} cfg.retryWithShapes cfg.proofFuel? with
    | .proof prf =>
      let proofTime := (← IO.monoMsNow) - beforeProof
      return some (prf, proofTime, result, goalContainsBinder)
    | .retryWithShapes => runEqSat goal rws guides { cfg with shapes := true } amb
  onEqSatFailure (cfg : Config) (goalContainsBinder : Bool) (report : Request.Result.Report) :
      Request.Failure → MetaM MessageData
    | .backend msg? => do
      let mut msg := msg?
      if msg.isEmpty then
        let reasonMsg := if report.reasonMsg.isEmpty then "" else s!": {report.reasonMsg}"
        msg := s!"egg failed to prove the goal ({report.stopReason.description}{reasonMsg}) "
      unless cfg.reporting do return msg
      return msg ++ formatReport cfg.flattenReports report (goalContainsBinder := goalContainsBinder)
    | .explLength len => do
      let msg := s!"egg found an explanation exceeding the length limit ({len} vs {cfg.explLengthLimit})\nYou can increase this limit using 'set_option egg.explLengthLimit <num>'.\n"
      unless cfg.reporting do return msg
      return msg ++ formatReport cfg.flattenReports report (goalContainsBinder := goalContainsBinder)

syntax &"egg " egg_cfg_mod egg_premises (egg_guides)? : tactic
elab_rules : tactic
  | `(tactic| egg $mod $prems $[$guides]?) => Egg.eval mod prems guides

-- WORKAROUND: This fixes `Tests/EndOfInput *`.
macro "egg " mod:egg_cfg_mod : tactic => `(tactic| egg $mod)

-- The syntax `egg!` calls egg with the global egg basket.
elab "egg! " mod:egg_cfg_mod prems:egg_premises guides:(egg_guides)? : tactic =>
  Egg.eval mod prems guides (basket? := `egg)

-- WORKAROUND: This fixes a problem analogous to `Tests/EndOfInput *` for `egg!`.
macro "egg! " mod:egg_cfg_mod : tactic => `(tactic| egg! $mod)

-- The syntax `egg?` calls calcify after running egg.
elab tk:"egg? " mod:egg_cfg_mod prems:egg_premises guides:(egg_guides)? : tactic =>
  Egg.eval mod prems guides (basket? := none) (calcifyTk? := tk)

-- WORKAROUND: This fixes a problem analogous to `Tests/EndOfInput *` for `egg?`.
macro "egg? " mod:egg_cfg_mod : tactic => `(tactic| egg? $mod)
