import Egg.Core.Explanation.Basic
open Lean

namespace Egg.Explanation

declare_syntax_cat lit
declare_syntax_cat shape
declare_syntax_cat shift_offset
declare_syntax_cat dir
declare_syntax_cat rw_dir
declare_syntax_cat subexpr_pos
declare_syntax_cat basic_rw_src
declare_syntax_cat lean_rw_src
declare_syntax_cat defeq_rw_src
declare_syntax_cat tc_proj_loc
declare_syntax_cat tc_proj
declare_syntax_cat tc_spec_src
declare_syntax_cat tc_spec
declare_syntax_cat tc_extension
declare_syntax_cat explosion_extension
declare_syntax_cat fwd_rw_src
declare_syntax_cat rw_src
declare_syntax_cat weak_vars

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

syntax "#" noWs num (noWs "/" noWs num)? : basic_rw_src
syntax "∗" noWs num                      : basic_rw_src
syntax "⊢"                               : basic_rw_src
syntax "▰" noWs num                      : basic_rw_src
-- Note: We don't run rewrite generation after deriving guides, so a derived guide source can never
--       be part of a rewrite source.
syntax "↣" noWs num                        : basic_rw_src
syntax "◯" noWs num                        : basic_rw_src
syntax "□" noWs ident (noWs "/" noWs num)? : basic_rw_src

syntax "[" tc_proj_loc num "," num "]" : tc_proj

syntax "→"          : tc_spec_src
syntax "←"          : tc_spec_src
syntax "?"          : tc_spec_src
syntax "⊢" noWs num : tc_spec_src
syntax "<" tc_spec_src ">" : tc_spec

syntax tc_proj : tc_extension
syntax tc_spec : tc_extension

-- TODO: For some reason separating out the `←` and `→` into their own syntax category caused
--       problems.

syntax "💥→[" num,* "]" : explosion_extension
syntax "💥←[" num,* "]" : explosion_extension

syntax basic_rw_src                             : lean_rw_src
syntax basic_rw_src "<" num "⊢>"                : lean_rw_src
syntax basic_rw_src (noWs tc_extension)+        : lean_rw_src
syntax basic_rw_src noWs explosion_extension    : lean_rw_src
syntax basic_rw_src noWs "↓"                    : lean_rw_src
syntax "▵" noWs num                             : lean_rw_src

syntax "↦bvar"  : defeq_rw_src
syntax "↦app"   : defeq_rw_src
syntax "↦λ"     : defeq_rw_src
syntax "↦∀"     : defeq_rw_src
syntax "↦fvar"  : defeq_rw_src
syntax "↦mvar"  : defeq_rw_src
syntax "↦sort"  : defeq_rw_src
syntax "↦lit"   : defeq_rw_src
syntax "↦proof" : defeq_rw_src
syntax "↦inst"  : defeq_rw_src
syntax "↦_"     : defeq_rw_src
syntax "↦|"     : defeq_rw_src
syntax "↑bvar"  : defeq_rw_src
syntax "↑app"   : defeq_rw_src
syntax "↑λ"     : defeq_rw_src
syntax "↑∀"     : defeq_rw_src
syntax "↑fvar"  : defeq_rw_src
syntax "↑mvar"  : defeq_rw_src
syntax "↑sort"  : defeq_rw_src
syntax "↑lit"   : defeq_rw_src
syntax "↑proof" : defeq_rw_src
syntax "↑inst"  : defeq_rw_src
syntax "↑_"     : defeq_rw_src
syntax "≡maxS"  : defeq_rw_src
syntax "≡max↔"  : defeq_rw_src
syntax "≡imax0" : defeq_rw_src
syntax "≡imaxS" : defeq_rw_src
syntax "≡η"     : defeq_rw_src
syntax "≡η+"    : defeq_rw_src
syntax "≡β"     : defeq_rw_src
syntax "≡0"     : defeq_rw_src
syntax "≡→S"    : defeq_rw_src
syntax "≡S→"    : defeq_rw_src
syntax "≡+"     : defeq_rw_src
syntax "≡-"     : defeq_rw_src
syntax "≡*"     : defeq_rw_src
syntax "≡^"     : defeq_rw_src
syntax "≡/"     : defeq_rw_src
-- WORKAROUND: https://egraphs.zulipchat.com/#narrow/stream/375765-egg.2Fegglog/topic/.25.20in.20rule.20name
syntax str      : defeq_rw_src
-- syntax "≡%"  : defeq_rw_src

syntax ("," noWs num "=" num)* : weak_vars

syntax "→" lean_rw_src weak_vars : rw_src
syntax "←" lean_rw_src weak_vars : rw_src
syntax defeq_rw_src ("-rev")?    : rw_src
syntax &"="                      : rw_src
syntax &"∧"                      : rw_src

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

private def parseTcSpecSrc : (TSyntax `tc_spec_src) → Source.TcSpec
  | `(tc_spec_src|→)     => .dir .forward
  | `(tc_spec_src|←)     => .dir .backward
  | `(tc_spec_src|?)     => .cond
  | `(tc_spec_src|⊢$idx) => .goalType idx.getNat
  | _                    => unreachable!

private def parseTcProjLocation : (TSyntax `tc_proj_loc) → Source.TcProjLocation
  | `(tc_proj_loc|▪)        => .root
  | `(tc_proj_loc|◂)        => .left
  | `(tc_proj_loc|▸)        => .right
  | `(tc_proj_loc|$n:num ?) => .cond n.getNat
  | _                       => unreachable!

private def parseBasicRwSrc : (TSyntax `basic_rw_src) → Source
  | `(basic_rw_src|#$idx$[/$eqn?]?)  => .explicit idx.getNat (eqn?.map TSyntax.getNat)
  | `(basic_rw_src|□$name$[/$eqn?]?) => .tagged name.getId (eqn?.map TSyntax.getNat)
  | `(basic_rw_src|∗$idx)            => .star (.fromUniqueIdx idx.getNat)
  | `(basic_rw_src|⊢)                => .goal
  | `(basic_rw_src|▰$idx)            => .intro idx.getNat
  | `(basic_rw_src|↣$idx)            => .guide idx.getNat (derived := false)
  | `(basic_rw_src|◯$idx)            => .builtin idx.getNat
  | _                                => unreachable!

private def parseTcExtension (src : Source) : (TSyntax `tc_extension) → Source
  | `(tc_extension|[$loc$pos,$dep]) => .tcProj src (parseTcProjLocation loc) pos.getNat dep.getNat
  | `(tc_extension|<$tcSpecsrc>)    => .tcSpec src (parseTcSpecSrc tcSpecsrc)
  | _                               => unreachable!

private def parseLeanRwSrc : (TSyntax `lean_rw_src) → Source
  | `(lean_rw_src|▵$idx)  => .structProj idx.getNat
  | `(lean_rw_src|$src:basic_rw_src) =>
    parseBasicRwSrc src
  | `(lean_rw_src|$src:basic_rw_src<$idx⊢>) =>
    .goalTypeSpec (parseBasicRwSrc src) idx.getNat
  | `(lean_rw_src|$src:basic_rw_src$tcExts:tc_extension*) =>
    tcExts.foldl (init := parseBasicRwSrc src) parseTcExtension
  | `(lean_rw_src|$src:basic_rw_src💥→[$idxs:num,*]) =>
    .explosion (parseBasicRwSrc src) .forward (idxs.getElems.map (·.getNat)).toList
  | `(lean_rw_src|$src:basic_rw_src💥←[$idxs:num,*]) =>
    .explosion (parseBasicRwSrc src) .backward (idxs.getElems.map (·.getNat)).toList
  | `(lean_rw_src|$src:basic_rw_src↓) => .ground (parseBasicRwSrc src)
  | _ => unreachable!

private def parseDefeqRwSrc : (TSyntax `defeq_rw_src) → Source
  | `(defeq_rw_src|↦bvar)  => .subst .bvar
  | `(defeq_rw_src|↦app)   => .subst .app
  | `(defeq_rw_src|↦λ)     => .subst .lam
  | `(defeq_rw_src|↦∀)     => .subst .forall
  | `(defeq_rw_src|↦fvar)  => .subst .fvar
  | `(defeq_rw_src|↦mvar)  => .subst .mvar
  | `(defeq_rw_src|↦sort)  => .subst .sort
  | `(defeq_rw_src|↦lit)   => .subst .lit
  | `(defeq_rw_src|↦proof) => .subst .proof
  | `(defeq_rw_src|↦inst)  => .subst .inst
  | `(defeq_rw_src|↦_)     => .subst .unknown
  | `(defeq_rw_src|↦|)     => .subst .abort
  | `(defeq_rw_src|↑bvar)  => .shift .bvar
  | `(defeq_rw_src|↑app)   => .shift .app
  | `(defeq_rw_src|↑λ)     => .shift .lam
  | `(defeq_rw_src|↑∀)     => .shift .forall
  | `(defeq_rw_src|↑fvar)  => .shift .fvar
  | `(defeq_rw_src|↑mvar)  => .shift .mvar
  | `(defeq_rw_src|↑sort)  => .shift .sort
  | `(defeq_rw_src|↑lit)   => .shift .lit
  | `(defeq_rw_src|↑proof) => .shift .proof
  | `(defeq_rw_src|↑inst)  => .shift .inst
  | `(defeq_rw_src|↑_)     => .shift .unknown
  | `(defeq_rw_src|≡maxS)  => .level .maxSucc
  | `(defeq_rw_src|≡max↔)  => .level .maxComm
  | `(defeq_rw_src|≡imax0) => .level .imaxZero
  | `(defeq_rw_src|≡imaxS) => .level .imaxSucc
  | `(defeq_rw_src|≡η)     => .eta false
  | `(defeq_rw_src|≡η+)    => .eta true
  | `(defeq_rw_src|≡β)     => .beta
  | `(defeq_rw_src|≡0)     => .natLit .zero
  | `(defeq_rw_src|≡→S)    => .natLit .toSucc
  | `(defeq_rw_src|≡S→)    => .natLit .ofSucc
  | `(defeq_rw_src|≡+)     => .natLit .add
  | `(defeq_rw_src|≡-)     => .natLit .sub
  | `(defeq_rw_src|≡*)     => .natLit .mul
  | `(defeq_rw_src|≡^)     => .natLit .pow
  | `(defeq_rw_src|≡/)     => .natLit .div
  | `(defeq_rw_src|"≡%")   => .natLit .mod
  | _ => unreachable!

def parseRwSrc : (TSyntax `rw_src) → Rewrite.Descriptor
  | `(rw_src|→$src:lean_rw_src$[,$weakVars=$weakClasses]*) => {
      src      := parseLeanRwSrc src
      srcDir   := .forward
      dir      := .forward
      weakVars := weakVars.zip weakClasses |>.map fun (v, c) => (v.getNat, c.getNat)
    }
  | `(rw_src|←$src:lean_rw_src$[,$weakVars=$weakClasses]*) => {
      src      := parseLeanRwSrc src
      srcDir   := .backward
      dir      := .forward
      weakVars := weakVars.zip weakClasses |>.map fun (v, c) => (v.getNat, c.getNat)
    }
  | `(rw_src|$src:defeq_rw_src$[-rev%$tk]?) => {
      src    := parseDefeqRwSrc src,
      srcDir := .forward,
      dir    := if tk.isSome then .backward else .forward, weakVars := #[]
    }
  | `(rw_src|=) => { src := .reifiedEq, srcDir := .forward, dir := .forward, weakVars := #[] }
  | `(rw_src|∧) => { src := .factAnd, srcDir := .forward, dir := .forward, weakVars := #[] }
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
    | nonDefeqTypeRw  => s!"{msgPrefix} step contains non-defeq type-level rewrite in proof or type class instance"

abbrev ParseStepM := ExceptT ParseError <| StateM (Option Rewrite.Info)
