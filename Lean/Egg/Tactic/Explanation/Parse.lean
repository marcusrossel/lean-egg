import Egg.Core.Explanation

open Lean

namespace Egg.Explanation

declare_syntax_cat egg_expl
declare_syntax_cat egg_expl_step
declare_syntax_cat egg_lvl
declare_syntax_cat egg_lit
declare_syntax_cat egg_rw_dir
declare_syntax_cat egg_side
declare_syntax_cat egg_subexpr_pos
declare_syntax_cat egg_basic_fwd_rw_src
declare_syntax_cat egg_fwd_rw_src
declare_syntax_cat egg_tc_proj
declare_syntax_cat egg_rw_src

syntax num                             : egg_lvl
syntax "(" &"uvar" num ")"             : egg_lvl
syntax "(" &"param" ident ")"          : egg_lvl
syntax "(" &"succ" egg_lvl ")"         : egg_lvl
syntax "(" &"max" egg_lvl egg_lvl ")"  : egg_lvl
syntax "(" &"imax" egg_lvl egg_lvl ")" : egg_lvl

syntax num : egg_lit
syntax str : egg_lit

syntax "=>" : egg_rw_dir
syntax "<=" : egg_rw_dir

syntax ident : egg_side

syntax "/"        : egg_subexpr_pos
syntax ("/" num)+ : egg_subexpr_pos

syntax "#" noWs num (noWs "/" noWs num)? : egg_basic_fwd_rw_src
syntax "*" noWs num                      : egg_basic_fwd_rw_src

syntax "[" egg_side egg_subexpr_pos "]" : egg_tc_proj

syntax egg_basic_fwd_rw_src (egg_tc_proj)? : egg_fwd_rw_src
syntax "⊢" egg_tc_proj                     : egg_fwd_rw_src
syntax "!z"                                : egg_fwd_rw_src
syntax "!t"                                : egg_fwd_rw_src
syntax "!o"                                : egg_fwd_rw_src
syntax "src/lib.rs:" num ":" num           : egg_fwd_rw_src -- TODO: https://egraphs.zulipchat.com/#narrow/stream/375765-egg.2Fegglog/topic/egg.3A.20dynamic.20rewrite's.20name

syntax egg_fwd_rw_src (noWs "-rev")? : egg_rw_src

-- Note: This syntax allows quite a few invalid constructions which we only handle in the parsing
--       functions below. For example, expression type tags should never contain a "Rewrite", but we
--       just ignore this.

syntax "(" &"bvar" num ")"                                         : egg_expl_step
syntax "(" &"fvar" num ")"                                         : egg_expl_step
syntax "(" &"mvar" num ")"                                         : egg_expl_step
syntax "(" &"sort" egg_lvl ")"                                     : egg_expl_step
syntax "(" &"const" ident egg_lvl* ")"                             : egg_expl_step
syntax "(" &"app" egg_expl_step egg_expl_step ")"                  : egg_expl_step
syntax "(" &"λ" egg_expl_step ")"                                  : egg_expl_step
syntax "(" &"∀" egg_expl_step ")"                                  : egg_expl_step
syntax "(" &"lit" egg_lit ")"                                      : egg_expl_step
syntax "(" &"Rewrite" noWs egg_rw_dir egg_rw_src egg_expl_step ")" : egg_expl_step
-- TODO: A more efficient way of handling type tags would be to declare a separate category for them
--       where one case is `num` and the other is an expression of the form `(.*)` such that parens
--       are balanced.
syntax "(" &"τ" (num <|> egg_expl_step) egg_expl_step ")"          : egg_expl_step

syntax egg_expl_step+ : egg_expl

private partial def parseLevel : (TSyntax `egg_lvl) → Level
  | `(egg_lvl|$n:num)             => n.getNat.toLevel
  | `(egg_lvl|(uvar $id))         => .mvar (.fromUniqueIdx id.getNat)
  | `(egg_lvl|(param $n))         => .param n.getId
  | `(egg_lvl|(succ $lvl))        => .succ (parseLevel lvl)
  | `(egg_lvl|(max $lvl₁ $lvl₂))  => .max (parseLevel lvl₁) (parseLevel lvl₂)
  | `(egg_lvl|(imax $lvl₁ $lvl₂)) => .imax (parseLevel lvl₁) (parseLevel lvl₂)
  | _                             => unreachable!

private def parseLit : (TSyntax `egg_lit) → Literal
  | `(egg_lit|$n:num) => .natVal n.getNat
  | `(egg_lit|$s:str) => .strVal s.getString
  | _                 => unreachable!

private def parseRwDir : (TSyntax `egg_rw_dir) → Rewrite.Direction
  | `(egg_rw_dir|=>) => .forward
  | `(egg_rw_dir|<=) => .backward
  | _                => unreachable!

private def parseSide : (TSyntax `egg_side) → Side
  | `(egg_side|l) => .left
  | `(egg_side|r) => .right
  | _             => unreachable!

private def parseSubexprPos : (TSyntax `egg_subexpr_pos) → SubExpr.Pos
  | `(egg_subexpr_pos|/)        => .root
  | `(egg_subexpr_pos|$[/$ps]*) => SubExpr.Pos.ofArray <| ps.map (·.getNat)
  | _                           => unreachable!

private def parseBasicFwdRwSrc : (TSyntax `egg_basic_fwd_rw_src) → Source
  | `(egg_basic_fwd_rw_src|#$idx$[/$eqn?]?) => .explicit idx.getNat (eqn?.map TSyntax.getNat)
  | `(egg_basic_fwd_rw_src|*$idx)           => .star (.fromUniqueIdx idx.getNat)
  | _                                       => unreachable!

private def parseFwdRwSrc : (TSyntax `egg_fwd_rw_src) → Source
  | `(egg_fwd_rw_src|$src:egg_basic_fwd_rw_src)            => parseBasicFwdRwSrc src
  | `(egg_fwd_rw_src|$src:egg_basic_fwd_rw_src[$side$pos]) => .tcProj (parseBasicFwdRwSrc src) (parseSide side) (parseSubexprPos pos)
  | `(egg_fwd_rw_src|⊢[$side$pos])                         => .tcProj .goal (parseSide side) (parseSubexprPos pos)
  | `(egg_fwd_rw_src|!z)                                   => .natLit .zero
  | `(egg_fwd_rw_src|!t)                                   => .natLit .toSucc
  | `(egg_fwd_rw_src|!o)                                   => .natLit .ofSucc
  | `(egg_fwd_rw_src|src/lib.rs: $_ : $_)                  => .natLit .zero -- TODO: https://egraphs.zulipchat.com/#narrow/stream/375765-egg.2Fegglog/topic/egg.3A.20dynamic.20rewrite's.20name
  | _                                                      => unreachable!

private def parseRwSrc : (TSyntax `egg_rw_src) → Rewrite.Descriptor
  | `(egg_rw_src|$fwdSrc:egg_fwd_rw_src)     => { src := parseFwdRwSrc fwdSrc, dir := .forward }
  | `(egg_rw_src|$fwdSrc:egg_fwd_rw_src-rev) => { src := parseFwdRwSrc fwdSrc, dir := .backward }
  | _                                        => unreachable!

inductive ParseError where
  | noSteps
  | startContainsRw
  | stepMissingRw
  | stepContainsMultipleRws
  deriving Inhabited

private def ParseError.msgPrefix :=
  "egg failed to parse explanation:"

open ParseError in
instance : Coe ParseError MessageData where
  coe
    | noSteps                 => s!"{msgPrefix} no steps found"
    | startContainsRw         => s!"{msgPrefix} start contains a rewrite"
    | stepMissingRw           => s!"{msgPrefix} (non-start) step does not contain a rewrite"
    | stepContainsMultipleRws => s!"{msgPrefix} step contains multiple rewrites"

private abbrev ParseStepResult := Except ParseError <| Expression × (Option Rewrite.Info)
private abbrev ParseStepM := ExceptT ParseError <| StateM (Option Rewrite.Info)

private partial def parseExplStep (stx : TSyntax `egg_expl_step) : ParseStepResult :=
  let (e, info?) := go .root stx |>.run none
  return (← e, info?)
where
  go (pos : SubExpr.Pos) : (TSyntax `egg_expl_step) → ParseStepM Expression
    | `(egg_expl_step|(bvar $idx))              => return .bvar idx.getNat
    | `(egg_expl_step|(fvar $id))               => return .fvar (.fromUniqueIdx id.getNat)
    | `(egg_expl_step|(mvar $id))               => return .mvar (.fromUniqueIdx id.getNat)
    | `(egg_expl_step|(sort $lvl))              => return .sort (parseLevel lvl)
    | `(egg_expl_step|(const $name $lvls*))     => return .const name.getId (lvls.map parseLevel)
    | `(egg_expl_step|(app $fn $arg))           => return .app (← go pos.pushAppFn fn) (← go pos.pushAppArg arg)
    | `(egg_expl_step|(λ $body))                => return .lam (← go pos.pushBindingBody body)
    | `(egg_expl_step|(∀ $body))                => return .forall (← go pos.pushBindingBody body)
    | `(egg_expl_step|(lit $l))                 => return .lit (parseLit l)
    | `(egg_expl_step|(Rewrite$dir $src $body)) => parseRw dir src body pos
    | `(egg_expl_step|(τ $_ $e))                => go pos e
    | _                                         => unreachable!

  parseRw (dir : TSyntax `egg_rw_dir) (src : TSyntax `egg_rw_src) (body : TSyntax `egg_expl_step)
      (pos : SubExpr.Pos) : ParseStepM Expression := do
    unless (← get).isNone do throw .stepContainsMultipleRws
    let info := parseRwSrc src
    let dir := info.dir.merge (parseRwDir dir)
    set <| some { info with dir, pos : Rewrite.Info }
    go pos body

private def parseExpl : (TSyntax `egg_expl) → Except ParseError Explanation
  | `(egg_expl|$steps:egg_expl_step*) => do
    let some start := steps[0]? | throw .noSteps
    let .ok (start, none) := parseExplStep start | throw .startContainsRw
    let mut tl : Array Step := #[]
    for step in steps[1:] do
      let (dst, some info) ← parseExplStep step | throw .stepMissingRw
      tl := tl.push { info with dst }
    return { start, steps := tl }
  | _ => unreachable!

-- Note: This could be generalized to any monad with an environment and exceptions.
def parse (str : String) : CoreM Explanation := do
  match Parser.runParserCategory (← getEnv) `egg_expl str with
  | .ok stx    =>
    match parseExpl ⟨stx⟩ with
    | .ok expl => return expl
    | .error err => throwError err
  | .error err => throwError s!"{ParseError.msgPrefix}\n{err}"
