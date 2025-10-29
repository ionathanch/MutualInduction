import Lean.Parser.Term
import Lean.Parser.Command

namespace Lean.Macro

open Lean.Parser.Term
open Lean.Parser.Command

declare_syntax_cat theoremDecl
declare_syntax_cat binder

syntax "theorem " declId ppIndent(declSig) : theoremDecl
syntax (name := joint)
  "joint" (ident <|> hole <|> bracketedBinder)*
    theoremDecl+ byTactic' : command

def binderKinds : SyntaxNodeKinds :=
  [`ident, `Lean.Parser.Term.hole, `Lean.Parser.Term.bracketedBinder]

structure TheoremDecl where
  name : TSyntax `ident
  univs : TSyntaxArray `ident
  vars : TSyntaxArray binderKinds
  binders : TSyntaxArray binderKinds
  sig : TSyntax `term

instance : Coe (TSyntax binderKinds) (TSyntax `Lean.Parser.Term.funBinder) where
  coe stx := ⟨stx.raw⟩

def mkThmPair (thm : TheoremDecl) : MacroM (TSyntax `term) := do
  `(PSigma.mk _ (λ $thm.vars* $thm.binders* ↦ @id $thm.sig ?$thm.name))

def mkJointName (names : Array Name) : Name :=
  match names.foldl append (Name.mkStr1 "") with
  | .str n s | .num n s => .str n s!"{s}_"
  | n => n
  where append : Name → Name → Name
    | .str n s₁, .str _ s₂
    | .str n s₁, .num _ s₂ =>
      .str n s!"{s₁}_{s₂}"
    | n, _ => n

def mkJointDef (byTk : Syntax) (thms : Array TheoremDecl) (tactics : Syntax.TSepArray `tactic "") :
    MacroM (Command × TSyntax `ident) := do
  let name := mkJointName (thms.map (·.name.getId))
  let tid : Ident := mkIdent name
  let pairs ← thms.mapM mkThmPair
  let byBlock ← withRef byTk `(term| by refine #[$pairs,*]; $tactics*)
  let defn ← `(command| def $tid : Array (PSigma fun (A : Sort _) ↦ A) := $byBlock)
  return (defn, tid)

def mkNthThm (id : TSyntax `ident) (n : Nat) (thm : TheoremDecl) : MacroM Command := do
  let nstx := Syntax.mkNatLit n
  if thm.univs.isEmpty then
    `(command| theorem $thm.name : ∀ $thm.vars* $thm.binders*, $thm.sig := $id[$nstx].snd)
  else
    `(command| theorem $thm.name.{$thm.univs,*} : ∀ $thm.vars* $thm.binders*, $thm.sig := $id[$nstx].snd)

@[macro «joint»]
def expandJoint : Macro := λ stx ↦ do
  match stx with
  | `(command| joint $vars* $thms:theoremDecl* by%$byTk $tactics:tactic*) =>
    let thmDecls ← thms.mapM (λ (thm : TSyntax `theoremDecl) ↦ do
      match thm with
      | `(theoremDecl| theorem $name.{$univs,*} $binders* : $sig) =>
        dbg_trace (name, univs.getElems, binders, sig)
        return {name, univs := univs.getElems, vars, binders, sig : TheoremDecl}
      | `(theoremDecl| theorem $name:ident $binders* : $sig) =>
        dbg_trace (name, binders, sig)
        return {name, univs := #[], vars, binders, sig : TheoremDecl}
      | _ => throwUnsupported)
    let (jointDef, name) ← mkJointDef byTk thmDecls tactics
    let nthThms ← thmDecls.mapIdxM (mkNthThm name)
    return mkNullNode (#[jointDef] ++ nthThms)
  | _ => throwUnsupported

end Macro
