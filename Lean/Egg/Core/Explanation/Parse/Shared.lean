import Egg.Core.Explanation.Basic
open Lean

namespace Egg.Explanation

declare_syntax_cat lit
declare_syntax_cat shape
declare_syntax_cat shift_offset
declare_syntax_cat dir
declare_syntax_cat rw_dir
declare_syntax_cat subexpr_pos
declare_syntax_cat basic_fwd_rw_src
declare_syntax_cat tc_proj_loc
declare_syntax_cat tc_proj
declare_syntax_cat tc_spec_src
declare_syntax_cat tc_spec
declare_syntax_cat tc_extension
declare_syntax_cat explosion
declare_syntax_cat fwd_rw_src
declare_syntax_cat fact_src
declare_syntax_cat rw_src

syntax num : lit
syntax str : lit

syntax "*"                  : shape
syntax "(→" shape shape ")" : shape

syntax "=>" : rw_dir
syntax "<=" : rw_dir

syntax "▪"     : tc_proj_loc
syntax "◂"     : tc_proj_loc
syntax "▸"     : tc_proj_loc
syntax num "?" : tc_proj_loc

syntax "#" noWs num (noWs "/" noWs num)? : basic_fwd_rw_src
syntax "*" noWs num                      : basic_fwd_rw_src
syntax "⊢"                               : basic_fwd_rw_src
syntax "↣" noWs num                      : basic_fwd_rw_src
syntax "◯" noWs num                      : basic_fwd_rw_src
syntax "□" noWs num (noWs "/" noWs num)? : basic_fwd_rw_src

syntax "[" tc_proj_loc num "," num "]" : tc_proj

syntax "→" : tc_spec_src
syntax "←" : tc_spec_src
syntax "?" : tc_spec_src
syntax "⊢" : tc_spec_src
syntax "<" tc_spec_src ">" : tc_spec

syntax tc_proj : tc_extension
syntax tc_spec : tc_extension

-- TODO: For some reason separating out the `←` and `→` into their own syntax category caused
--       problems.
syntax "💥→[" num,* "]" : explosion
syntax "💥←[" num,* "]" : explosion

syntax basic_fwd_rw_src (noWs tc_extension)* : fwd_rw_src
syntax basic_fwd_rw_src noWs explosion       : fwd_rw_src
syntax "↦bvar"                               : fwd_rw_src
syntax "↦app"                                : fwd_rw_src
syntax "↦λ"                                  : fwd_rw_src
syntax "↦∀"                                  : fwd_rw_src
syntax "↦fvar"                               : fwd_rw_src
syntax "↦mvar"                               : fwd_rw_src
syntax "↦sort"                               : fwd_rw_src
syntax "↦lit"                                : fwd_rw_src
syntax "↦proof"                              : fwd_rw_src
syntax "↦inst"                               : fwd_rw_src
syntax "↦_"                                  : fwd_rw_src
syntax "↦|"                                  : fwd_rw_src
syntax "↑bvar"                               : fwd_rw_src
syntax "↑app"                                : fwd_rw_src
syntax "↑λ"                                  : fwd_rw_src
syntax "↑∀"                                  : fwd_rw_src
syntax "↑fvar"                               : fwd_rw_src
syntax "↑mvar"                               : fwd_rw_src
syntax "↑sort"                               : fwd_rw_src
syntax "↑lit"                                : fwd_rw_src
syntax "↑proof"                              : fwd_rw_src
syntax "↑inst"                               : fwd_rw_src
syntax "↑_"                                  : fwd_rw_src
syntax "≡maxS"                               : fwd_rw_src
syntax "≡max↔"                               : fwd_rw_src
syntax "≡imax0"                              : fwd_rw_src
syntax "≡imaxS"                              : fwd_rw_src
syntax "≡η"                                  : fwd_rw_src
syntax "≡η+"                                 : fwd_rw_src
syntax "≡β"                                  : fwd_rw_src
syntax "≡0"                                  : fwd_rw_src
syntax "≡→S"                                 : fwd_rw_src
syntax "≡S→"                                 : fwd_rw_src
syntax "≡+"                                  : fwd_rw_src
syntax "≡-"                                  : fwd_rw_src
syntax "≡*"                                  : fwd_rw_src
syntax "≡^"                                  : fwd_rw_src
syntax "≡/"                                  : fwd_rw_src
-- WORKAROUND: https://egraphs.zulipchat.com/#narrow/stream/375765-egg.2Fegglog/topic/.25.20in.20rule.20name
syntax str                                   : fwd_rw_src
-- syntax "≡%"                               : fwd_rw_src

syntax "!?"           : fact_src
syntax "!" fwd_rw_src : fact_src

syntax fwd_rw_src (noWs "-rev")? fact_src* : rw_src

syntax "+" num : shift_offset
syntax "-" num : shift_offset

def parseLit : (TSyntax `lit) → Literal
  | `(lit|$n:num) => .natVal n.getNat
  | `(lit|$s:str) => .strVal s.getString
  | _             => unreachable!

def parseShiftOffset : (TSyntax `shift_offset) → Int
  | `(shift_offset|+ $n:num) => n.getNat
  | `(shift_offset|- $n:num) => -n.getNat
  | _                        => unreachable!

def parseRwDir : (TSyntax `rw_dir) → Direction
  | `(rw_dir|=>) => .forward
  | `(rw_dir|<=) => .backward
  | _                => unreachable!

private def parsTcSpecSrc : (TSyntax `tc_spec_src) → Source.TcSpec
  | `(tc_spec_src|→) => .dir .forward
  | `(tc_spec_src|←) => .dir .backward
  | `(tc_spec_src|?) => .cond
  | `(tc_spec_src|⊢) => .goalType
  | _                => unreachable!

private def parseTcProjLocation : (TSyntax `tc_proj_loc) → Source.TcProjLocation
  | `(tc_proj_loc|▪)        => .root
  | `(tc_proj_loc|◂)        => .left
  | `(tc_proj_loc|▸)        => .right
  | `(tc_proj_loc|$n:num ?) => .cond n.getNat
  | _                       => unreachable!

private def parseBasicFwdRwSrc : (TSyntax `basic_fwd_rw_src) → Source
  | `(basic_fwd_rw_src|#$idx$[/$eqn?]?) => .explicit idx.getNat (eqn?.map TSyntax.getNat)
  | `(basic_fwd_rw_src|□$idx$[/$eqn?]?) => .tagged idx.getNat (eqn?.map TSyntax.getNat)
  | `(basic_fwd_rw_src|*$idx)           => .star (.fromUniqueIdx idx.getNat)
  | `(basic_fwd_rw_src|⊢)               => .goal
  | `(basic_fwd_rw_src|↣$idx)           => .guide idx.getNat
  | `(basic_fwd_rw_src|◯$idx)           => .builtin idx.getNat
  | _                                   => unreachable!

private def parseTcExtension (src : Source) : (TSyntax `tc_extension) → Source
  | `(tc_extension|[$loc$pos,$dep]) => .tcProj src (parseTcProjLocation loc) pos.getNat dep.getNat
  | `(tc_extension|<$tcSpecsrc>)    => .tcSpec src (parsTcSpecSrc tcSpecsrc)
  | _                               => unreachable!

private def parseFwdRwSrc : (TSyntax `fwd_rw_src) → Source
  | `(fwd_rw_src|↦bvar)  => .subst .bvar
  | `(fwd_rw_src|↦app)   => .subst .app
  | `(fwd_rw_src|↦λ)     => .subst .lam
  | `(fwd_rw_src|↦∀)     => .subst .forall
  | `(fwd_rw_src|↦fvar)  => .subst .fvar
  | `(fwd_rw_src|↦mvar)  => .subst .mvar
  | `(fwd_rw_src|↦sort)  => .subst .sort
  | `(fwd_rw_src|↦lit)   => .subst .lit
  | `(fwd_rw_src|↦proof) => .subst .proof
  | `(fwd_rw_src|↦inst)  => .subst .inst
  | `(fwd_rw_src|↦_)     => .subst .unknown
  | `(fwd_rw_src|↦|)     => .subst .abort
  | `(fwd_rw_src|↑bvar)  => .shift .bvar
  | `(fwd_rw_src|↑app)   => .shift .app
  | `(fwd_rw_src|↑λ)     => .shift .lam
  | `(fwd_rw_src|↑∀)     => .shift .forall
  | `(fwd_rw_src|↑fvar)  => .shift .fvar
  | `(fwd_rw_src|↑mvar)  => .shift .mvar
  | `(fwd_rw_src|↑sort)  => .shift .sort
  | `(fwd_rw_src|↑lit)   => .shift .lit
  | `(fwd_rw_src|↑proof) => .shift .proof
  | `(fwd_rw_src|↑inst)  => .shift .inst
  | `(fwd_rw_src|↑_)     => .shift .unknown
  | `(fwd_rw_src|≡maxS)  => .level .maxSucc
  | `(fwd_rw_src|≡max↔)  => .level .maxComm
  | `(fwd_rw_src|≡imax0) => .level .imaxZero
  | `(fwd_rw_src|≡imaxS) => .level .imaxSucc
  | `(fwd_rw_src|≡η)     => .eta false
  | `(fwd_rw_src|≡η+)    => .eta true
  | `(fwd_rw_src|≡β)     => .beta
  | `(fwd_rw_src|≡0)     => .natLit .zero
  | `(fwd_rw_src|≡→S)    => .natLit .toSucc
  | `(fwd_rw_src|≡S→)    => .natLit .ofSucc
  | `(fwd_rw_src|≡+)     => .natLit .add
  | `(fwd_rw_src|≡-)     => .natLit .sub
  | `(fwd_rw_src|≡*)     => .natLit .mul
  | `(fwd_rw_src|≡^)     => .natLit .pow
  | `(fwd_rw_src|≡/)     => .natLit .div
  | `(fwd_rw_src|"≡%")   => .natLit .mod
  | `(fwd_rw_src|$src:basic_fwd_rw_src$tcExts:tc_extension*) =>
    tcExts.foldl (init := parseBasicFwdRwSrc src) parseTcExtension
  | `(fwd_rw_src|$src:basic_fwd_rw_src💥→[$idxs:num,*]) =>
    .explosion (parseBasicFwdRwSrc src) .forward (idxs.getElems.map (·.getNat)).toList
  | `(fwd_rw_src|$src:basic_fwd_rw_src💥←[$idxs:num,*]) =>
    .explosion (parseBasicFwdRwSrc src) .backward (idxs.getElems.map (·.getNat)).toList
  | _ => unreachable!

private def parseFactSrc : (TSyntax `fact_src) → Option Source
  | `(fact_src|!?)             => none
  | `(fact_src|!$f:fwd_rw_src) => some <| .fact (parseFwdRwSrc f)
  | _                          => unreachable!

def parseRwSrc : (TSyntax `rw_src) → Rewrite.Descriptor
  | `(rw_src|$fwdSrc:fwd_rw_src$[-rev%$rev]?$[$facts]*) =>
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
  | nonDefeqTypeRw
  deriving Inhabited

def ParseError.msgPrefix :=
  "egg received invalid explanation:"

open ParseError in
instance : Coe ParseError MessageData where
  coe
    | noSteps         => s!"{msgPrefix} no steps found"
    | startContainsRw => s!"{msgPrefix} start contains a rewrite"
    | missingRw       => s!"{msgPrefix} (non-start) step does not contain a rewrite"
    | multipleRws     => s!"{msgPrefix} step contains multiple rewrites"
    | nonDefeqTypeRw  => s!"{msgPrefix} step contains non-defeq type-level rewrite in proof or inst"

abbrev ParseStepM := ExceptT ParseError <| StateM (Option Rewrite.Info)
