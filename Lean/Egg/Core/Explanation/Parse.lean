import Egg.Core.Explanation.Basic
import Egg.Core.Explanation.Flatten
import Std

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

syntax "$" num : egg_slot

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

syntax "(" &"bvar" egg_slot ")"                            : egg_expr
syntax "(" &"fvar" num ")"                                 : egg_expr
syntax "(" &"mvar" num ")"                                 : egg_expr
syntax "(" &"sort" egg_lvl ")"                             : egg_expr
syntax "(" &"const" ident egg_lvl* ")" : egg_expr
syntax "(" &"app" egg_expr egg_expr ")"                    : egg_expr
syntax "(" &"λ" egg_slot egg_expr egg_expr ")"             : egg_expr
syntax "(" &"∀" egg_slot egg_expr egg_expr ")"             : egg_expr
syntax "(" &"lit" egg_lit ")"                              : egg_expr
syntax "(" &"proof" egg_expr ")"                           : egg_expr
-- TODO: syntax "(" &"↦" num egg_expr egg_expr ")"         : egg_expr
-- TODO: syntax "(" &"↑" egg_shift_offset num egg_expr ")" : egg_expr
syntax "(" "◇" egg_shape egg_expr ")"                      : egg_expr
syntax egg_lvl                                             : egg_expr
syntax egg_shape                                           : egg_expr

syntax "refl"                             : egg_justification
syntax "symmetry" "(" num ")"             : egg_justification
syntax "transitivity" "(" num "," num ")" : egg_justification
syntax "congruence" "(" num,+ ")"         : egg_justification
syntax "Some" "(" egg_rw_src ")"          : egg_justification

syntax num ": " egg_expr " = " egg_expr "by " egg_justification : egg_lemma

syntax egg_lemma+ : egg_expl

private def parseSlot : (TSyntax `egg_slot) → Nat
  | `(egg_slot|$ $n) => n.getNat
  | _                => unreachable!

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
  | `(egg_justification|Some($src))                 => .rw (parseRwSrc src)
  | _                                               => unreachable!

private partial def parseLevel : (TSyntax `egg_lvl) → Level
  | `(egg_lvl|$n:num)             => n.getNat.toLevel
  | `(egg_lvl|(uvar $id))         => .mvar (.fromUniqueIdx id.getNat)
  | `(egg_lvl|(param $n))         => .param n.getId
  | `(egg_lvl|(succ $lvl))        => .succ (parseLevel lvl)
  | `(egg_lvl|(max $lvl₁ $lvl₂))  => .max (parseLevel lvl₁) (parseLevel lvl₂)
  | `(egg_lvl|(imax $lvl₁ $lvl₂)) => .imax (parseLevel lvl₁) (parseLevel lvl₂)
  | _                             => unreachable!

private inductive ParseExprResult where
  | expr   (e : Expression)
  | shaped (e : Expression)
  | shape
  deriving Inhabited

private def ParseExprResult.expr! : ParseExprResult → Expression
  | expr e | shaped e => e
  | shape => panic! "called 'ParseExprResult.expr!' on `ParseExprResult.shape`"

private partial def parseExpr : (TSyntax `egg_expr) → ParseExprResult
  | `(egg_expr|(bvar $id))           => .expr <| .bvar (parseSlot id)
  | `(egg_expr|(fvar $id))           => .expr <| .fvar (.fromUniqueIdx id.getNat)
  | `(egg_expr|(mvar $id))           => .expr <| .mvar (.fromUniqueIdx id.getNat)
  | `(egg_expr|(sort $lvl))          => .expr <| .sort (parseLevel lvl)
  | `(egg_expr|(const $name $lvls*)) => .expr <| .const name.getId (lvls.map parseLevel).toList
  | `(egg_expr|(app $fn $arg))       => .expr <| .app (parseExpr fn).expr! (parseExpr arg).expr!
  | `(egg_expr|(λ $var $ty $body))   => .expr <| .lam (parseSlot var) (parseExpr ty).expr! (parseExpr body).expr!
  | `(egg_expr|(∀ $var $ty $body))   => .expr <| .forall (parseSlot var) (parseExpr ty).expr! (parseExpr body).expr!
  | `(egg_expr|(lit $l))             => .expr <| .lit (parseLit l)
  | `(egg_expr|(proof $p))           => .expr <| .proof (parseExpr p).expr!
  -- TODO: | `(egg_expr|(↦ $idx $to $e))  => return .subst idx.getNat (← go pos to) (← go pos e)
  -- TODO: | `(egg_expr|(↑ $off $cut $e)) => return .shift (parseShiftOffset off) cut.getNat (← go pos e)
  | `(egg_expr|(◇ $_ $e))            => .shaped (parseExpr e).expr!
  | `(egg_expr|$lvl:egg_lvl)         => .expr <| .lvl (parseLevel lvl)
  | `(egg_expr|$_:egg_shape)         => .shape
  | _                                => unreachable!

private inductive ParseLemmaResult where
  | lem (idx : Nat) (lem : Lemma)
  | redirect («from» to : Nat)
  | erase
  deriving Inhabited

-- If the lemma is `none`, this indicates an erased lemma. If the associated `Nat` is set, the lemma
-- is replaced by another lemmas with that index.
private def parseLemma : (TSyntax `egg_lemma) → ParseLemmaResult
  | `(egg_lemma|$n:num : $lhs = $rhs by $jus) =>
    let jus := parseJustification jus
    match parseExpr lhs, parseExpr rhs with
    | .expr lhs,   .expr rhs   => .lem n.getNat  { lhs, rhs, jus }
    | .shaped lhs, .shaped rhs => if let .congr #[_, r] := jus then .redirect n.getNat r else .lem n.getNat { lhs, rhs, jus }
    | .shape,      .shape      => .erase
    | _,           _           => panic! "'Egg.Explanation.parseLemma' got different results from 'parseExpr'"
  | _ => unreachable!

private partial def parseExplTree : (TSyntax `egg_expl) → Option Explanation.Tree
  | `(egg_expl|$lems:egg_lemma*) => do
    let mut lemmas : Std.HashMap Nat Lemma := ∅
    let mut redirects : Std.HashMap Nat Nat := ∅
    for lem in lems do
      match parseLemma lem with
      | .erase              => continue
      | .redirect «from» to => redirects := redirects.insert «from» to
       -- This approach assumes that lemmas are parsed in order of their indices.
      | .lem idx lem        => lemmas := lemmas.insert idx { lem with jus := applyRedirects redirects lem.jus }
    let some target := lemmas.keys.maximum? | failure
    return { lemmas, target }
  | _ => unreachable!
where
  applyRedirects (r : Std.HashMap Nat Nat) : Justification → Justification
    | .symm i      => .symm (redirectIdx r i)
    | .trans i₁ i₂ => .trans (redirectIdx r i₁) (redirectIdx r i₂)
    | .congr is    => .congr <| is.map (redirectIdx r)
    | j            => j
  redirectIdx (r : Std.HashMap Nat Nat) (idx : Nat) : Nat :=
    match r[idx]? with
    | none   => idx
    | some i => redirectIdx r i

-- Note: This could be generalized to any monad with an environment and exceptions.
def Raw.parse (raw : Explanation.Raw) : CoreM Explanation := do
  let raw := raw.replace "\"" "" -- HACK
  match Parser.runParserCategory (← getEnv) `egg_expl raw with
  | .ok stx =>
    let some expl := parseExplTree ⟨stx⟩
      | throwError "egg internal error: called 'Explanation.Raw.parse' on an empty explanation"
    match expl.flatten with
    | .ok expl   => return expl
    | .error err => throwError err.description
  | .error err => throwError s!"egg received invalid explanation:\n{err}\n\n{raw}"
