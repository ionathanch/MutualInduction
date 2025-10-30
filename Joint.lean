import Lean.Parser.Term
import Lean.Parser.Command

namespace Lean.Macro

open Lean.Parser.Term
open Lean.Parser.Command

declare_syntax_cat theoremDecl

syntax "theorem " ident ppIndent(declSig) : theoremDecl
def binder := bracketedBinder (requireType := true)

syntax (name := joint)
  "joint" (".{" ident,+ "}")? binder*
    theoremDecl+ byTactic' : command

def binderKinds : SyntaxNodeKinds :=
  [`ident, `Lean.Parser.Term.hole, `Lean.Parser.Term.bracketedBinder]

instance : Coe (TSyntax binderKinds) (TSyntax `Lean.Parser.Term.funBinder) where
  coe stx := ⟨stx.raw⟩

structure JointVars where
  univs : TSyntaxArray `ident
  binders : TSyntaxArray `Lean.Parser.Term.bracketedBinder

structure TheoremDecl where
  /-- Syntax object of `theorem` keyword -/
  stx : Syntax
  name : TSyntax `ident
  binders : TSyntaxArray binderKinds
  /-- Result type of declaration -/
  sig : TSyntax `term

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

/-- Get the bound variable `x` in a typed bracketed binder
`(x : A)`, `{x : A}`, `⦃x : A⦄`, or `{{x : A}}`. -/
def getBoundVars (binder : TSyntax `Lean.Parser.Term.bracketedBinder) : TSyntaxArray `ident :=
  match binder with
  | `(binder|  ($xs:ident* : $_:term))
  | `(binder|  {$xs:ident* : $_:term})
  | `(binder|  ⦃$xs:ident* : $_:term⦄)
  | `(binder| {{$xs:ident* : $_:term}}) => xs
  | _ => #[]

/--
Given a theorem declaration of the form
  `theorem thm (x : A)... : B`,
create the pair
  `⟨(∀ (x : A)..., B), (λ (x : A)... ↦ ?thm)⟩`
of type `(Σ' A : Sort _, A)`.
-/
def mkThmPair (thm : TheoremDecl) : MacroM (TSyntax `term) := do
  `(PSigma.mk (∀ $thm.binders*, $thm.sig) (λ $thm.binders* ↦ ?$thm.name))

/--
Given `n` theorems `thmᵢ : Aᵢ`, create a definition named `_thm₁_..._thmₙ_`
with a heterogeneous array of proofs of `Aᵢ`.
The body of the definition is a refined array of holes `?thmᵢ : A_i`
that should then be solved by the given `tactics`.
-/
def mkJointDef (jnt : JointVars) (thms : Array TheoremDecl) (byTk : Syntax) (tactics : Syntax.TSepArray `tactic "") :
    MacroM (Command × TSyntax `ident) := do
  let id := mkIdent <| mkJointName (thms.map (·.name.getId))
  let pairs ← thms.mapM mkThmPair
  let byBlock ← withRef byTk `(term| by refine #[$pairs,*]; $tactics*)
  let defn ←
    if jnt.univs.isEmpty then
      `(command| abbrev $id $jnt.binders* : Array (PSigma fun (A : Sort _) ↦ A) := $byBlock)
    else
      `(command| abbrev $id.{$jnt.univs,*} $jnt.binders* : Array (PSigma fun (A : Sort _) ↦ A) := $byBlock)
  return (defn, id)

/--
The `i`th theorem is proven by the `i`th element of the jointly defined array:
  `theorem thmₙ : Aₙ := _thm₁_..._thmₙ_[i].snd`.
Note it must be that `_thm₁_..._thmₙ_[i].fst = Aₙ`.
-/
def mkNthThm (id : TSyntax `ident) (jnt : JointVars) (i : Nat) (thm : TheoremDecl) : MacroM Command := do
  let istx := Syntax.mkNatLit i
  let args := Array.flatten <| jnt.binders.map getBoundVars
  let nthThm ← withRef thm.stx <|
    if jnt.univs.isEmpty then
      `(command| theorem $thm.name $jnt.binders* : ∀ $thm.binders*, $thm.sig := (@$id $args*)[$istx].snd)
    else
      `(command| theorem $thm.name.{$jnt.univs,*} $jnt.binders* : ∀ $thm.binders*, $thm.sig := (@$id.{$jnt.univs,*} $args*)[$istx].snd)
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
  match stx with
  | `(command| joint$[.{$univs,*}]? $vars* $thms:theoremDecl* by%$byTk $tactics:tactic*) =>
    let jointVars : JointVars := {univs := univs.getD {}, binders := vars}
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
