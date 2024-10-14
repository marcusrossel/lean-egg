import Egg.Core.Explanation.Basic

open Lean Parser

namespace Egg.Explanation

declare_syntax_cat egg_expl
declare_syntax_cat egg_justification
declare_syntax_cat egg_lemma
declare_syntax_cat egg_expr
declare_syntax_cat egg_lvl
declare_syntax_cat egg_slot
declare_syntax_cat egg_lit
declare_syntax_cat egg_shape
declare_syntax_cat egg_shift_offset
declare_syntax_cat egg_dir
declare_syntax_cat egg_rw_dir
declare_syntax_cat egg_subexpr_pos
declare_syntax_cat egg_basic_fwd_rw_src
declare_syntax_cat egg_tc_proj_loc
declare_syntax_cat egg_tc_proj
declare_syntax_cat egg_tc_spec_src
declare_syntax_cat egg_tc_spec
declare_syntax_cat egg_tc_extension
declare_syntax_cat egg_explosion
declare_syntax_cat egg_fwd_rw_src
declare_syntax_cat egg_fact_src
declare_syntax_cat egg_rw_src

syntax num : egg_lit
syntax str : egg_lit

syntax ident : egg_slot

syntax "*"                          : egg_shape
syntax "(→" egg_shape egg_shape ")" : egg_shape

syntax "▪"     : egg_tc_proj_loc
syntax "◂"     : egg_tc_proj_loc
syntax "▸"     : egg_tc_proj_loc
syntax num "?" : egg_tc_proj_loc

syntax "#" noWs num (noWs "/" noWs num)? : egg_basic_fwd_rw_src
syntax "*" noWs num                      : egg_basic_fwd_rw_src
syntax "⊢"                               : egg_basic_fwd_rw_src
syntax "↣" noWs num                      : egg_basic_fwd_rw_src
syntax "◯" noWs num                      : egg_basic_fwd_rw_src
syntax "□" noWs num (noWs "/" noWs num)? : egg_basic_fwd_rw_src

syntax "[" egg_tc_proj_loc num "," num "]" : egg_tc_proj

syntax "→" : egg_tc_spec_src
syntax "←" : egg_tc_spec_src
syntax "?" : egg_tc_spec_src
syntax "⊢" : egg_tc_spec_src
syntax "<" egg_tc_spec_src ">" : egg_tc_spec

syntax egg_tc_proj : egg_tc_extension
syntax egg_tc_spec : egg_tc_extension

-- TODO: For some reason separating out the `←` and `→` into their own syntax category caused
--       problems.
syntax "💥→[" num,* "]" : egg_explosion
syntax "💥←[" num,* "]" : egg_explosion

syntax egg_basic_fwd_rw_src (noWs egg_tc_extension)* : egg_fwd_rw_src
syntax egg_basic_fwd_rw_src noWs egg_explosion       : egg_fwd_rw_src
syntax "↦bvar"                                       : egg_fwd_rw_src
syntax "↦app"                                        : egg_fwd_rw_src
syntax "↦λ"                                          : egg_fwd_rw_src
syntax "↦∀"                                          : egg_fwd_rw_src
syntax "↑bvar"                                       : egg_fwd_rw_src
syntax "↑app"                                        : egg_fwd_rw_src
syntax "↑λ"                                          : egg_fwd_rw_src
syntax "↑∀"                                          : egg_fwd_rw_src
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

syntax "!?"               : egg_fact_src
syntax "!" egg_fwd_rw_src : egg_fact_src

syntax egg_fwd_rw_src (noWs "-rev")? egg_fact_src* : egg_rw_src

-- TODO: syntax "+" num : egg_shift_offset
-- TODO: syntax "-" num : egg_shift_offset

syntax num                             : egg_lvl
syntax "(" &"uvar" num ")"             : egg_lvl
syntax "(" &"param" ident ")"          : egg_lvl
syntax "(" &"succ" egg_lvl ")"         : egg_lvl
syntax "(" &"max" egg_lvl egg_lvl ")"  : egg_lvl
syntax "(" &"imax" egg_lvl egg_lvl ")" : egg_lvl

syntax egg_lvl                                             : egg_expr
syntax "(" &"bvar" egg_slot ")"                            : egg_expr
syntax "(" &"fvar" num ")"                                 : egg_expr
syntax "(" &"mvar" num ")"                                 : egg_expr
syntax "(" &"sort" egg_lvl ")"                             : egg_expr
syntax "(" &"const" ident egg_lvl* ")"                     : egg_expr
syntax "(" &"app" egg_expr egg_expr ")"                    : egg_expr
syntax "(" &"λ" egg_slot egg_expr egg_expr ")"             : egg_expr
syntax "(" &"∀" egg_slot egg_expr egg_expr ")"             : egg_expr
syntax "(" &"lit" egg_lit ")"                              : egg_expr
syntax "(" &"proof" egg_expr ")"                           : egg_expr
-- TODO: syntax "(" &"↦" num egg_expr egg_expr ")"         : egg_expr
-- TODO: syntax "(" &"↑" egg_shift_offset num egg_expr ")" : egg_expr
syntax "(" "◇" egg_shape egg_expr ")"                      : egg_expr

local syntax "refl"                                            : egg_justification
local syntax "symmetry" "(" num ")"                            : egg_justification
local syntax "transitivity" "(" num "," num ")"                : egg_justification
local syntax "congruence" "(" num,+ ")"                        : egg_justification
local syntax "Some" "(" doubleQuote egg_rw_src doubleQuote ")" : egg_justification

local syntax "lemma" noWs num ": " singleQuote egg_expr " = " egg_expr singleQuote &"by " egg_justification : egg_lemma

syntax egg_lemma+ : egg_expl

private def parseLit : (TSyntax `egg_lit) → Literal
  | `(egg_lit|$n:num) => .natVal n.getNat
  | `(egg_lit|$s:str) => .strVal s.getString
  | _                 => unreachable!

/- TODO:
private def parseShiftOffset : (TSyntax `egg_shift_offset) → Int
  | `(egg_shift_offset|+ $n:num) => n.getNat
  | `(egg_shift_offset|- $n:num) => -n.getNat
  | _                            => unreachable!
-/

private def parsTcSpecSrc : (TSyntax `egg_tc_spec_src) → Source.TcSpec
  | `(egg_tc_spec_src|→) => .dir .forward
  | `(egg_tc_spec_src|←) => .dir .backward
  | `(egg_tc_spec_src|?) => .cond
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
  | `(egg_basic_fwd_rw_src|□$idx$[/$eqn?]?) => .tagged idx.getNat (eqn?.map TSyntax.getNat)
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
  -- TODO: | `(egg_fwd_rw_src|↦bvar)  => return .subst .bvar
  -- TODO: | `(egg_fwd_rw_src|↦app)   => return .subst .app
  -- TODO: | `(egg_fwd_rw_src|↦λ)     => return .subst .lam
  -- TODO: | `(egg_fwd_rw_src|↦∀)     => return .subst .forall
  -- TODO: | `(egg_fwd_rw_src|↑bvar)  => return .shift .bvar
  -- TODO: | `(egg_fwd_rw_src|↑app)   => return .shift .app
  -- TODO: | `(egg_fwd_rw_src|↑λ)     => return .shift .lam
  -- TODO: | `(egg_fwd_rw_src|↑∀)     => return .shift .forall
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
  | `(egg_fwd_rw_src|$src:egg_basic_fwd_rw_src💥→[$idxs:num,*]) =>
    .explosion (parseBasicFwdRwSrc src) .forward (idxs.getElems.map (·.getNat)).toList
  | `(egg_fwd_rw_src|$src:egg_basic_fwd_rw_src💥←[$idxs:num,*]) =>
    .explosion (parseBasicFwdRwSrc src) .backward (idxs.getElems.map (·.getNat)).toList
  | _ => unreachable!

private def parseFactSrc : (TSyntax `egg_fact_src) → Option Source
  | `(egg_fact_src|!?)                 => none
  | `(egg_fact_src|!$f:egg_fwd_rw_src) => some <| .fact (parseFwdRwSrc f)
  | _                                  => unreachable!

private def parseRwSrc : (TSyntax `egg_rw_src) → Rewrite.Descriptor
  | `(egg_rw_src|$fwdSrc:egg_fwd_rw_src$[-rev%$rev]?$[$facts]*) => {
      src   := parseFwdRwSrc fwdSrc
      dir   := if rev.isSome then .backward else .forward
      facts := facts.map parseFactSrc
    }
  | _ => unreachable!

private def parseJustification : (TSyntax `egg_justification) → Justification
  | `(egg_justification|refl)                       => .rfl
  | `(egg_justification|symmetry($lem))             => .symm lem.getNat
  | `(egg_justification|transitivity($lem₁, $lem₂)) => .trans lem₁.getNat lem₂.getNat
  | `(egg_justification|congruence($lems,*))        => .congr <| lems.getElems.map (·.getNat)
  | `(egg_justification|Some("$src"))               => .rw (parseRwSrc src)
  | _                                               => unreachable!

private partial def parseLevel : (TSyntax `egg_lvl) → Level
  | `(egg_lvl|$n:num)             => n.getNat.toLevel
  | `(egg_lvl|(uvar $id))         => .mvar (.fromUniqueIdx id.getNat)
  | `(egg_lvl|(param $n))         => .param n.getId
  | `(egg_lvl|(succ $lvl))        => .succ (parseLevel lvl)
  | `(egg_lvl|(max $lvl₁ $lvl₂))  => .max (parseLevel lvl₁) (parseLevel lvl₂)
  | `(egg_lvl|(imax $lvl₁ $lvl₂)) => .imax (parseLevel lvl₁) (parseLevel lvl₂)
  | _                             => unreachable!

private partial def parseExpr : (TSyntax `egg_expr) → Expression
  | `(egg_expr|$lvl:egg_lvl)             => .lvl (parseLevel lvl)
  | `(egg_expr|(bvar $id:ident))         => .bvar id.getId
  | `(egg_expr|(fvar $id))               => .fvar (.fromUniqueIdx id.getNat)
  | `(egg_expr|(mvar $id))               => .mvar (.fromUniqueIdx id.getNat)
  | `(egg_expr|(sort $lvl))              => .sort (parseLevel lvl)
  | `(egg_expr|(const $name $lvls*))     => .const name.getId (lvls.map parseLevel).toList
  | `(egg_expr|(app $fn $arg))           => .app (parseExpr fn) (parseExpr arg)
  | `(egg_expr|(λ $var:ident $ty $body)) => .lam var.getId (parseExpr ty) (parseExpr body)
  | `(egg_expr|(∀ $var:ident $ty $body)) => .forall var.getId (parseExpr ty) (parseExpr body)
  | `(egg_expr|(lit $l))                 => .lit (parseLit l)
  | `(egg_expr|(proof $p))               => .proof (parseExpr p)
  -- TODO: | `(egg_expr|(↦ $idx $to $e))  => return .subst idx.getNat (← go pos to) (← go pos e)
  -- TODO: | `(egg_expr|(↑ $off $cut $e)) => return .shift (parseShiftOffset off) cut.getNat (← go pos e)
  | `(egg_expr|(◇ $_ $e))                => parseExpr e
  | _                                    => unreachable!

private def parseLemma : (TSyntax `egg_lemma) → Lemma
  | `(egg_lemma|lemma$_ : ' $lhs = $rhs ' by $jus) => {
      lhs := parseExpr lhs
      rhs := parseExpr rhs
      jus := parseJustification jus
    }
  | _ => unreachable!

private def parseExpl : (TSyntax `egg_expl) → Option Explanation
  | `(egg_expl|$lems:egg_lemma*) => do
    let lems := lems.map parseLemma
    let some target := lems[lems.size - 1]? | failure
    return { lemmas := lems[:lems.size - 2], target }
  | _ => unreachable!

-- Note: This could be generalized to any monad with an environment and exceptions.
def Raw.parse (raw : Explanation.Raw) : CoreM Explanation := do
  match Parser.runParserCategory (← getEnv) `egg_expl raw with
  | .ok stx =>
    let some expl := parseExpl ⟨stx⟩
      | throwError "egg internal error: called 'Explanation.Raw.parse' on an empty explanation"
    return expl
  | .error err => throwError s!"egg received invalid explanation:\n{err}\n\n{raw}"
