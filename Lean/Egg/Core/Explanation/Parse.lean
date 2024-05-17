import Egg.Core.Explanation.Basic

open Lean

namespace Egg.Explanation

declare_syntax_cat egg_expl
declare_syntax_cat egg_rw_expr
declare_syntax_cat egg_rw_lvl
declare_syntax_cat egg_lit
declare_syntax_cat egg_rw_dir
declare_syntax_cat egg_subexpr_pos
declare_syntax_cat egg_basic_fwd_rw_src
declare_syntax_cat egg_tc_proj_loc
declare_syntax_cat egg_tc_proj
declare_syntax_cat egg_tc_spec_src
declare_syntax_cat egg_tc_spec
declare_syntax_cat egg_tc_extension
declare_syntax_cat egg_fwd_rw_src
declare_syntax_cat egg_fact_src
declare_syntax_cat egg_rw_src

syntax num : egg_lit
syntax str : egg_lit

syntax "=>" : egg_rw_dir
syntax "<=" : egg_rw_dir

syntax "▪"     : egg_tc_proj_loc
syntax "◂"     : egg_tc_proj_loc
syntax "▸"     : egg_tc_proj_loc
syntax num "?" : egg_tc_proj_loc

syntax "#" noWs num (noWs "/" noWs num)? : egg_basic_fwd_rw_src
syntax "*" noWs num                      : egg_basic_fwd_rw_src
syntax "⊢"                               : egg_basic_fwd_rw_src
syntax "↣" noWs num                      : egg_basic_fwd_rw_src
syntax "◯" noWs num                      : egg_basic_fwd_rw_src

syntax "[" egg_tc_proj_loc num "," num "]" : egg_tc_proj

syntax "→" : egg_tc_spec_src
syntax "←" : egg_tc_spec_src
syntax "⊢" : egg_tc_spec_src
syntax "<" egg_tc_spec_src ">" : egg_tc_spec

syntax egg_tc_proj : egg_tc_extension
syntax egg_tc_spec : egg_tc_extension

syntax egg_basic_fwd_rw_src (noWs egg_tc_extension)* : egg_fwd_rw_src
syntax "≡maxS"                                       : egg_fwd_rw_src
syntax "≡max↔"                                       : egg_fwd_rw_src
syntax "≡imax0"                                      : egg_fwd_rw_src
syntax "≡imaxS"                                      : egg_fwd_rw_src
syntax "≡η"                                          : egg_fwd_rw_src
syntax "≡β"                                          : egg_fwd_rw_src
syntax "≡0"                                          : egg_fwd_rw_src
syntax "≡→S"                                         : egg_fwd_rw_src
syntax "≡S→"                                         : egg_fwd_rw_src
syntax "≡+"                                          : egg_fwd_rw_src
syntax "≡-"                                          : egg_fwd_rw_src
syntax "≡*"                                          : egg_fwd_rw_src
syntax "≡^"                                          : egg_fwd_rw_src
syntax "≡/"                                          : egg_fwd_rw_src
-- WORKAROUND: https://egraphs.zulipchat.com/#narrow/stream/375765-egg.2Fegglog/topic/.25.20in.20rule.20name
syntax str                                           : egg_fwd_rw_src
-- syntax "≡%"                                       : egg_fwd_rw_src

syntax "!" egg_fwd_rw_src : egg_fact_src

syntax egg_fwd_rw_src (noWs "-rev")? egg_fact_src* : egg_rw_src

syntax num                                                      : egg_rw_lvl
syntax "(" &"uvar" num ")"                                      : egg_rw_lvl
syntax "(" &"param" ident ")"                                   : egg_rw_lvl
syntax "(" &"succ" egg_rw_lvl ")"                               : egg_rw_lvl
syntax "(" &"max" egg_rw_lvl egg_rw_lvl ")"                     : egg_rw_lvl
syntax "(" &"imax" egg_rw_lvl egg_rw_lvl ")"                    : egg_rw_lvl
syntax "(" &"Rewrite" noWs egg_rw_dir egg_rw_src egg_rw_lvl ")" : egg_rw_lvl

syntax "_"                                                       : egg_rw_expr
syntax "(" &"bvar" num ")"                                       : egg_rw_expr
syntax "(" &"fvar" num ")"                                       : egg_rw_expr
syntax "(" &"mvar" num ")"                                       : egg_rw_expr
syntax "(" &"sort" egg_rw_lvl ")"                                : egg_rw_expr
syntax "(" &"const" ident egg_rw_lvl* ")"                        : egg_rw_expr
syntax "(" &"app" egg_rw_expr egg_rw_expr ")"                    : egg_rw_expr
syntax "(" &"λ" egg_rw_expr egg_rw_expr ")"                      : egg_rw_expr
syntax "(" &"∀" egg_rw_expr egg_rw_expr ")"                      : egg_rw_expr
syntax "(" &"lit" egg_lit ")"                                    : egg_rw_expr
syntax "(" &"Rewrite" noWs egg_rw_dir egg_rw_src egg_rw_expr ")" : egg_rw_expr

syntax egg_rw_expr+ : egg_expl

private def parseLit : (TSyntax `egg_lit) → Literal
  | `(egg_lit|$n:num) => .natVal n.getNat
  | `(egg_lit|$s:str) => .strVal s.getString
  | _                 => unreachable!

private def parseRwDir : (TSyntax `egg_rw_dir) → Direction
  | `(egg_rw_dir|=>) => .forward
  | `(egg_rw_dir|<=) => .backward
  | _                => unreachable!

private def parsTcSpecSrc : (TSyntax `egg_tc_spec_src) → Source.TcSpec
  | `(egg_tc_spec_src|→) => .dir .forward
  | `(egg_tc_spec_src|←) => .dir .backward
  | `(egg_tc_spec_src|⊢) => .goalType
  | _                    => unreachable!

private def parseTcProjLocation : (TSyntax `egg_tc_proj_loc) → Source.TcProjLocation
  | `(egg_tc_proj_loc|▪)        => .root
  | `(egg_tc_proj_loc|◂)        => .left
  | `(egg_tc_proj_loc|▸)        => .right
  | `(egg_tc_proj_loc|$n:num ?) => .cond n.getNat
  | _                           => unreachable!

private def parseBasicFwdRwSrc : (TSyntax `egg_basic_fwd_rw_src) → Source
  | `(egg_basic_fwd_rw_src|#$idx$[/$eqn?]?) => .explicit idx.getNat (eqn?.map TSyntax.getNat)
  | `(egg_basic_fwd_rw_src|*$idx)           => .star (.fromUniqueIdx idx.getNat)
  | `(egg_basic_fwd_rw_src|⊢)               => .goal
  | `(egg_basic_fwd_rw_src|↣$idx)           => .guide idx.getNat
  | `(egg_basic_fwd_rw_src|◯$idx)           => .builtin idx.getNat
  | _                                       => unreachable!

private def parseTcExtension (src : Source) : (TSyntax `egg_tc_extension) → Source
  | `(egg_tc_extension|[$loc$pos,$dep]) => .tcProj src (parseTcProjLocation loc) pos.getNat dep.getNat
  | `(egg_tc_extension|<$tcSpecsrc>)    => .tcSpec src (parsTcSpecSrc tcSpecsrc)
  | _                                   => unreachable!

private def parseFwdRwSrc : (TSyntax `egg_fwd_rw_src) → Source
  | `(egg_fwd_rw_src|≡maxS)  => .level .maxSucc
  | `(egg_fwd_rw_src|≡max↔)  => .level .maxComm
  | `(egg_fwd_rw_src|≡imax0) => .level .imaxZero
  | `(egg_fwd_rw_src|≡imaxS) => .level .imaxSucc
  | `(egg_fwd_rw_src|≡η)     => .eta
  | `(egg_fwd_rw_src|≡β)     => .beta
  | `(egg_fwd_rw_src|≡0)     => .natLit .zero
  | `(egg_fwd_rw_src|≡→S)    => .natLit .toSucc
  | `(egg_fwd_rw_src|≡S→)    => .natLit .ofSucc
  | `(egg_fwd_rw_src|≡+)     => .natLit .add
  | `(egg_fwd_rw_src|≡-)     => .natLit .sub
  | `(egg_fwd_rw_src|≡*)     => .natLit .mul
  | `(egg_fwd_rw_src|≡^)     => .natLit .pow
  | `(egg_fwd_rw_src|≡/)     => .natLit .div
  | `(egg_fwd_rw_src|"≡%")   => .natLit .mod
  | `(egg_fwd_rw_src|$src:egg_basic_fwd_rw_src$tcExts:egg_tc_extension*) =>
    tcExts.foldl (init := parseBasicFwdRwSrc src) parseTcExtension
  | _ => unreachable!

private def parseFactSrc : (TSyntax `egg_fact_src) → Source
  | `(egg_fact_src|!$f:egg_fwd_rw_src) => .fact (parseFwdRwSrc f)
  | _                                  => unreachable!

private def parseRwSrc : (TSyntax `egg_rw_src) → Rewrite.Descriptor
  | `(egg_rw_src|$fwdSrc:egg_fwd_rw_src$[-rev%$rev]?$[$facts]*) =>
    let src   := parseFwdRwSrc fwdSrc
    let dir   := if rev.isSome then .backward else .forward
    let facts := facts.map parseFactSrc
    { src, dir, facts }
  | _ => unreachable!

inductive ParseError where
  | noSteps
  | startContainsRw
  | missingRw
  | multipleRws
  deriving Inhabited

private def ParseError.msgPrefix :=
  "egg failed to parse explanation:"

open ParseError in
instance : Coe ParseError MessageData where
  coe
    | noSteps         => s!"{msgPrefix} no steps found"
    | startContainsRw => s!"{msgPrefix} start contains a rewrite"
    | missingRw       => s!"{msgPrefix} (non-start) step does not contain a rewrite"
    | multipleRws     => s!"{msgPrefix} step contains multiple rewrites"

private abbrev ParseStepResult := Except ParseError <| Expression × (Option Rewrite.Info)
private abbrev ParseStepM := ExceptT ParseError <| StateM (Option Rewrite.Info)

private partial def parseLevel : (TSyntax `egg_rw_lvl) → ParseStepM Level
  | `(egg_rw_lvl|$n:num)                   => return n.getNat.toLevel
  | `(egg_rw_lvl|(uvar $id))               => return .mvar (.fromUniqueIdx id.getNat)
  | `(egg_rw_lvl|(param $n))               => return .param n.getId
  | `(egg_rw_lvl|(succ $lvl))              => return .succ (← parseLevel lvl)
  | `(egg_rw_lvl|(max $lvl₁ $lvl₂))        => return .max (← parseLevel lvl₁) (← parseLevel lvl₂)
  | `(egg_rw_lvl|(imax $lvl₁ $lvl₂))       => return .imax (← parseLevel lvl₁) (← parseLevel lvl₂)
  | `(egg_rw_lvl|(Rewrite$dir $src $body)) => parseRw dir src body
  | _                                      => unreachable!
where
  parseRw (dir : TSyntax `egg_rw_dir) (src : TSyntax `egg_rw_src) (body : TSyntax `egg_rw_lvl) :
      ParseStepM Level := do
    unless (← get).isNone do throw .multipleRws
    let info := parseRwSrc src
    let dir := info.dir.merge (parseRwDir dir)
    set <| some { info with dir, pos? := none : Rewrite.Info }
    parseLevel body

private partial def parseExpr (stx : TSyntax `egg_rw_expr) : ParseStepResult :=
  let (e, info?) := go .root stx |>.run none
  return (← e, info?)
where
  go (pos : SubExpr.Pos) : (TSyntax `egg_rw_expr) → ParseStepM Expression
    | `(egg_rw_expr|_)                        => return .erased
    | `(egg_rw_expr|(bvar $idx))              => return .bvar idx.getNat
    | `(egg_rw_expr|(fvar $id))               => return .fvar (.fromUniqueIdx id.getNat)
    | `(egg_rw_expr|(mvar $id))               => return .mvar (.fromUniqueIdx id.getNat)
    | `(egg_rw_expr|(sort $lvl))              => return .sort (← parseLevel lvl)
    | `(egg_rw_expr|(const $name $lvls*))     => return .const name.getId (← lvls.mapM parseLevel).toList
    | `(egg_rw_expr|(app $fn $arg))           => return .app (← go pos.pushAppFn fn) (← go pos.pushAppArg arg)
    | `(egg_rw_expr|(λ $ty $body))            => return .lam (← go pos.pushBindingDomain ty) (← go pos.pushBindingBody body)
    | `(egg_rw_expr|(∀ $ty $body))            => return .forall (← go pos.pushBindingDomain ty) (← go pos.pushBindingBody body)
    | `(egg_rw_expr|(lit $l))                 => return .lit (parseLit l)
    | `(egg_rw_expr|(Rewrite$dir $src $body)) => parseRw dir src body pos
    | _                                         => unreachable!

  parseRw (dir : TSyntax `egg_rw_dir) (src : TSyntax `egg_rw_src) (body : TSyntax `egg_rw_expr)
      (pos : SubExpr.Pos) : ParseStepM Expression := do
    unless (← get).isNone do throw .multipleRws
    let info := parseRwSrc src
    let dir := info.dir.merge (parseRwDir dir)
    set <| some { info with dir, pos? := pos : Rewrite.Info }
    go pos body

private def parseExpl : (TSyntax `egg_expl) → Except ParseError Explanation
  | `(egg_expl|$steps:egg_rw_expr*) => do
    let some start := steps[0]? | throw .noSteps
    let .ok (start, none) := parseExpr start | throw .startContainsRw
    let mut tl : Array Step := #[]
    for step in steps[1:] do
      let (dst, some info) ← parseExpr step | throw .missingRw
      tl := tl.push { info with dst }
    return { start, steps := tl }
  | _ => unreachable!

-- Note: This could be generalized to any monad with an environment and exceptions.
def Raw.parse (raw : Explanation.Raw) : CoreM Explanation := do
  if "⚡️".isPrefixOf raw then
    throwError s!"egg backend failed:\n  {raw}"
  else
    match Parser.runParserCategory (← getEnv) `egg_expl raw with
    | .ok stx    =>
      match parseExpl ⟨stx⟩ with
      | .ok expl => return expl
      | .error err => throwError err
    | .error err => throwError s!"{ParseError.msgPrefix}\n{err}"
