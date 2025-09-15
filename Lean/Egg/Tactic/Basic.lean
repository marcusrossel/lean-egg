import Egg.Core.Request.Basic
import Egg.Core.Explanation.Proof
import Egg.Tactic.Config.Option
import Egg.Tactic.Config.Modifier
import Egg.Tactic.Goal
import Egg.Tactic.Guides
import Egg.Tactic.Rewrite.Rules.Gen.Basic
import Egg.Core.Gen.Guides
import Egg.Tactic.Trace
import Egg.Tactic.Calcify

open Lean Meta Elab Tactic

namespace Egg

private inductive Proof? where
  | proof (a : AbstractMVarsResult)
  | retryWithShapes

private def resultToProof
    (result : Request.Result) (goal : Goal) (rules : Rewrite.Rules) (cfg : Config.Encoding)
    (retryWithShapes subgoals : Bool) (proofFuel? : Option Nat) : TacticM Proof? := do
  let mut (proof, steps) ←
    try
      result.expl.prove' goal.toCongr rules result.egraph cfg subgoals proofFuel?
    catch err =>
      -- If proof reconstruction fails but we haven't tried using shapes yet, retry with shapes
      -- (assuming the corresponding option is enabled).
      if cfg.shapes || !retryWithShapes then
        throw err
      else
        return .retryWithShapes
  steps.trace rules.stxs `egg.proof
  proof ← instantiateMVars proof
  withTraceNode `egg.proof.term (fun _ => return "Proof Term") do trace[egg.proof.term] proof
  -- Note: This only abstracts mvars of the current mctx depth, which is exactly what we want.
  return .proof (← abstractMVars proof)

open Config.Modifier (egg_cfg_mod)

syntax egg_baskets := ("+" noWs ident)*

protected partial def eval
    (mod : TSyntax ``egg_cfg_mod) (args : TSyntax `egg_args)
    (guides : Option (TSyntax `egg_guides)) (baskets : TSyntax `Egg.egg_baskets)
    (calcifyTk? : Option Syntax := none) : TacticM Unit := do
  let save ← saveState
  try core catch err => restoreState save; throw err
where
  core : TacticM Unit := do
    let startTime ← IO.monoMsNow
    let goal ← getMainGoal
    let mod  ← Config.Modifier.parse mod
    let `(egg_baskets|$[+$baskets]*) := baskets | unreachable!
    let cfg := { (← Config.fromOptions).modify mod with baskets := baskets.map (·.getId) }
    cfg.trace `egg.config
    let goal ← Goal.gen goal
    goal.id.withContext do
      let guides := (← guides.mapM Guides.parseGuides).getD #[]
      -- We increase the mvar context depth, so that ambient mvars aren't unified during rewrite
      -- generation proof and reconstruction. Note that this also means that we can't assign the
      -- `goal` mvar inside of this `do`-block .
      let res ← withNewMCtxDepth (allowLevelAssignments := true) do
        let rules ← Rewrite.Rules.gen goal args guides cfg
        let mut guides := guides
        if cfg.derivedGuides then
            let rws := rules.entries.map (·.rw)
            guides := guides ++ (← genDerivedGuides goal.toCongr rws)
        withTraceNode `egg.guides (fun _ => return "Guides") do guides.trace `egg.guides
        runEqSat goal rules guides cfg
      match res with
      | some (proof, proofTime, result) =>
        if cfg.reporting then
          let totalTime := (← IO.monoMsNow) - startTime
          logInfo (s!"egg succeeded " ++ formatReport cfg.flattenReports result.report totalTime proofTime result.expl)
        let (subgoals, _, proof) ← openAbstractMVarsResult proof
        appendGoals <| Array.toList <| subgoals.map (·.mvarId!)
        goal.id.assignIfDefeq' proof
        if let some tk := calcifyTk? then calcify tk proof goal.intros.unzip.snd
      | none => goal.id.admit
  runEqSat
      (goal : Goal) (rules : Rewrite.Rules) (guides : Guides) (cfg : Config) :
      TacticM <| Option (AbstractMVarsResult × Nat × Request.Result) := do
    let req ← Request.encoding goal.toCongr rules guides #[] cfg
    withTraceNode `egg.encoded (fun _ => return "Encoded") do req.trace `egg.encoded
    if let .beforeEqSat := cfg.exitPoint then return none
    let result ← req.run cfg.explLengthLimit (onEqSatFailure cfg)
    result.expl.trace `egg.explanation.steps
    if let .beforeProof := cfg.exitPoint then return none
    let beforeProof ← IO.monoMsNow
    match ← resultToProof result goal rules cfg cfg.retryWithShapes cfg.subgoals cfg.proofFuel? with
    | .proof prf =>
      let proofTime := (← IO.monoMsNow) - beforeProof
      return some (prf, proofTime, result)
    | .retryWithShapes => runEqSat goal rules guides { cfg with shapes := true }
  onEqSatFailure (cfg : Config) (report : Request.Result.Report) : Request.Failure → MetaM MessageData
    | .backend msg? => do
      let mut msg := msg?
      if msg.isEmpty then
        let reasonMsg := if report.reasonMsg.isEmpty then "" else s!": {report.reasonMsg}"
        msg := s!"egg failed to prove the goal ({report.stopReason.description}{reasonMsg}) "
      unless cfg.reporting do return msg
      return msg ++ formatReport cfg.flattenReports report
    | .explLength len => do
      let msg := s!"egg found an explanation exceeding the length limit ({len} vs {cfg.explLengthLimit})\nYou can increase this limit using 'set_option egg.explLengthLimit <num>'.\n"
      unless cfg.reporting do return msg
      return msg ++ formatReport cfg.flattenReports report

elab "egg " baskets:egg_baskets mod:egg_cfg_mod args:egg_args guides:(egg_guides)? : tactic =>
  Egg.eval mod args guides baskets

-- WORKAROUND: This fixes `Tests/EndOfInput *`.
macro "egg " baskets:egg_baskets mod:egg_cfg_mod : tactic =>
  `(tactic| egg $baskets $mod:egg_cfg_mod)

-- The syntax `egg?` calls calcify after running egg.
elab tk:"egg? " baskets:egg_baskets mod:egg_cfg_mod args:egg_args guides:(egg_guides)? : tactic =>
  Egg.eval mod args guides baskets (calcifyTk? := tk)

-- WORKAROUND: This fixes a problem analogous to `Tests/EndOfInput *` for `egg?`.
macro "egg? " baskets:egg_baskets mod:egg_cfg_mod : tactic =>
  `(tactic| egg? $baskets $mod:egg_cfg_mod)
