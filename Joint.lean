import Lean.Parser.Term
import Lean.Parser.Command

namespace Lean.Macro

open Lean.Parser.Term
open Lean.Parser.Command

declare_syntax_cat theoremDecl

syntax "theorem " ident ppIndent(declSig) : theoremDecl
syntax (name := joint)
  "joint" (".{" ident,+ "}")? (ident <|> hole <|> bracketedBinder)*
    theoremDecl+ byTactic' : command

def binderKinds : SyntaxNodeKinds :=
  [`ident, `Lean.Parser.Term.hole, `Lean.Parser.Term.bracketedBinder]

structure JointVars where
  univs : TSyntaxArray `ident
  binders : TSyntaxArray binderKinds

structure TheoremDecl where
  /-- Syntax object of `theorem` keyword -/
  stx : Syntax
  name : TSyntax `ident
  binders : TSyntaxArray binderKinds
  /-- Result type of declaration -/
  sig : TSyntax `term

instance : Coe (TSyntax binderKinds) (TSyntax `Lean.Parser.Term.funBinder) where
  coe stx := ⟨stx.raw⟩

/--
Given a theorem declaration of the form
  `theorem thm (x : A)... : B`,
create the pair
  `⟨(∀ (x : A)..., B), (λ (x : A)... ↦ ?thm)⟩`
of type `(Σ' A : Sort _, A)`.
-/
def mkThmPair (jnt : JointVars) (thm : TheoremDecl) : MacroM (TSyntax `term) := do
  `(PSigma.mk (∀ $jnt.binders* $thm.binders*, $thm.sig) (λ $jnt.binders* $thm.binders* ↦ ?$thm.name))

/-- Join a sequence of names by underscores,
preceded and postceded by underscores. -/
def mkJointName (names : Array Name) : Name :=
  match names.foldl append (Name.mkStr1 "") with
  | .str n s | .num n s => .str n s!"{s}_"
  | n => n
  where append : Name → Name → Name
    | .str n s₁, .str _ s₂
    | .str n s₁, .num _ s₂ =>
      .str n s!"{s₁}_{s₂}"
    | n, _ => n

/--
Given `n` theorems `thmᵢ : Aᵢ`, create a definition named `_thm₁_..._thmₙ_`
with a heterogeneous array of proofs of `Aᵢ`.
The body of the definition is a refined array of holes `?thmᵢ : A_i`
that should then be solved by the given `tactics`.
-/
def mkJointDef (jnt : JointVars) (thms : Array TheoremDecl) (byTk : Syntax) (tactics : Syntax.TSepArray `tactic "") :
    MacroM (Command × TSyntax `ident) := do
  let id := mkIdent <| mkJointName (thms.map (·.name.getId))
  let pairs ← thms.mapM (mkThmPair jnt)
  let byBlock ← withRef byTk `(term| by refine #[$pairs,*]; $tactics*)
  let defn ←
    if jnt.univs.isEmpty then
      `(command| abbrev $id : Array (PSigma fun (A : Sort _) ↦ A) := $byBlock)
    else
      `(command| abbrev $id.{$jnt.univs,*} : Array (PSigma fun (A : Sort _) ↦ A) := $byBlock)
  return (defn, id)

/--
The `i`th theorem is proven by the `i`th element of the jointly defined array:
  `theorem thmₙ : Aₙ := _thm₁_..._thmₙ_[i].snd`.
Note it must be that `_thm₁_..._thmₙ_[i].fst = Aₙ`.
-/
def mkNthThm (id : TSyntax `ident) (jnt : JointVars) (i : Nat) (thm : TheoremDecl) : MacroM Command := do
  let istx := Syntax.mkNatLit i
  let nthThm ← withRef thm.stx <|
    if jnt.univs.isEmpty then
      `(command| theorem $thm.name : ∀ $jnt.binders* $thm.binders*, $thm.sig := $id[$istx].snd)
    else
      `(command| theorem $thm.name.{$jnt.univs,*} : ∀ $jnt.binders* $thm.binders*, $thm.sig := $id.{$jnt.univs,*}[$istx].snd)
  `(command| set_option linter.unusedVariables false in $nthThm)

/--
Given theorem statements of the form `theorem thm (y : B)... : C`,
possibly sharing joint universe variables `u...` and term variables `(x : A)...`,
the joint theorem declaration
```
joint.{u...} (x : A)...
  theorem thm (y : B)... : C
  ...
by ...
```
enters a proof state containing each theorem as a separate goal.
This is different from `mutual` theorems because their bodies cannot be mutually recursive.

As an example, given the following joint theorem statements:
```
joint (n : Nat)
  theorem evenInv (h : isEven (n + 1)) : isOdd n
  theorem oddInv  (h : isOdd  (n + 1)) : isEven n
by ...
```
the proof environment contains two goals:
* `case evenInv` with state `n : Nat, h : isEven (n + 1) ⊢ isOdd n`, and
* `case oddInv`  with state `n : Nat, h : isOdd  (n + 1) ⊢ isEven n`.
-/
@[macro «joint»]
def expandJoint : Macro := λ stx ↦ do
  let univs : Syntax.TSepArray `ident "," := {}
  match stx with
  | `(command| joint $vars* $thms:theoremDecl* by%$byTk $tactics:tactic*)
  | `(command| joint.{$univs,*} $vars* $thms:theoremDecl* by%$byTk $tactics:tactic*) =>
    let jointVars : JointVars := {univs, binders := vars}
    let thmDecls ← thms.mapM (λ (thm : TSyntax `theoremDecl) ↦ do
      match thm with
      | `(theoremDecl| theorem%$thmTk $name:ident $binders* : $sig) =>
        return {stx := thmTk, name, binders, sig : TheoremDecl}
      | _ => throwUnsupported)
    let (jointDef, name) ← mkJointDef jointVars thmDecls byTk tactics
    let nthThms ← thmDecls.mapIdxM (mkNthThm name jointVars)
    return mkNullNode (#[jointDef] ++ nthThms)
  | _ => throwUnsupported

end Macro
