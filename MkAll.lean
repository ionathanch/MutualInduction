import Lean

namespace Lean.Meta.MkAll
open Meta

@[inline]
def nonstrictposMsg (ctor : Name) (α : Expr) :=
  m!"parameter {α} appears non-strictly-positively in constructor {ctor}"

/--
If a free variable `fv` from `fvs` appears in the types of `exprs`,
throw an error with a message about `fv`.
-/
def checkFVars {ρe ρf : Type → Type} [ForIn MetaM (ρe Expr) Expr] [ForIn MetaM (ρf Expr) Expr]
  (exprs : ρe Expr) (fvs : ρf Expr) (emsg : Expr → MessageData): MetaM Unit := do
  for expr in exprs do
    let exprType ← inferType expr
    for fv in fvs do
      if (collectFVars {} exprType).fvarSet.contains fv.fvarId! then
        throwError emsg fv

/--
For each parameter `α`, create a motive `α → Sort rlvl`,
and `k`ontinue with the parameters and the motives.
-/
def withLocalMotives {β} [Inhabited β] (αnames : Array Name) (rlvl : Level) (k : Array Expr → Array Expr → MetaM β) : MetaM β := do
  let mut motiveDecls : Array (Name × (Array Expr → MetaM Expr)) := #[]
  let mut params  : Array Expr := #[]
  for αname in αnames do
    let some (.cdecl _ αfvar _ αtype _ _) := (← getLCtx).findFromUserName? αname
      | throwError "unknown parameter {αname}"
    unless αtype.isSort do
      throwError "the type of parameter {αname} is not a sort"
    let motiveType := mkForall αname .default (.fvar αfvar) (.sort rlvl)
    let motiveName := αname.str "motive"
    motiveDecls := motiveDecls.push (motiveName, λ _ ↦ pure motiveType)
    params := params.push (.fvar αfvar)
  withLocalDeclsD motiveDecls (k params)

/--
Given a constructor `c` of an inductive type `I`, its type must have the following shape:
```
c : ∀ (param : paramType)... (field : fieldType)..., I param... index...
```
We wish to build the corresponding `I.all` constructor,
which for the selected parameters `α...` from `param...`
has as additional parameters `(motive_α : α → Prop)...`.
This constructor has the following shape:
```
c.all : ∀ (param : paramType)... (field : fieldType)... (newField : newFieldType)...,
        I.all param... motive_α... index... (c param... field...)
```
The new fields are built from the existing fields
when they return elements of `α...` or of `I`.
That is, if `fieldType` has the shape `∀ (arg : argType)..., appFn appArgs...`,
* When `appFn` is `α`,
  `newFieldType` is `∀ (arg : argType)..., motive_α (field arg...)`;
* When `appFn` is `I` and `appArgs` is `param... cindex...`,
  `newFieldType` is `∀ (arg : argType)..., I.all param... motive_α... cindex... (field arg...)`;

otherwise, no new field is added.
-/
def buildCtorType (all : Name) (αnames : Array Name) (indVal : InductiveVal) (ctorInfo : ConstructorVal) : MetaM Constructor := do
  let type ← forallTelescope ctorInfo.type fun ctorArgs ctorInd => do
    withLocalMotives αnames .zero fun αs motives => do
    let αmotives := List.zip αs.toList motives.toList
    assert! ctorArgs.size == ctorInfo.numParams + ctorInfo.numFields
    let params : Array Expr := ctorArgs[:ctorInfo.numParams]
    let fields : Array Expr := ctorArgs[ctorInfo.numParams:]
    let ⟨_, indArgs⟩ := ctorInd.getAppFnArgs
    assert! indArgs.size == indVal.numParams + indVal.numIndices
    let indices : Array Expr := indArgs[indVal.numParams:]
    let appCtor := mkAppN (.const ctorInfo.name (ctorInfo.levelParams.map .param)) ctorArgs
    let ctorType := mkAppN allExpr (params ++ motives ++ indices ++ #[appCtor])
    mkForallFVars (params ++ motives ++ fields) (← loop αmotives ctorType #[] fields.toList)
  pure { name := ctorInfo.name.updatePrefix all, type }
  where
  allExpr : Expr := .const all (indVal.levelParams.map .param)
  loop (αmotives : List (Expr × Expr)) (ctorType : Expr) (newFields : Array Expr) : List Expr → MetaM Expr
  | [] => mkForallFVars newFields ctorType
  | field :: fields => do
    let fieldType ← inferType field
    forallTelescope fieldType fun args type => do
      checkFVars args (αmotives.map (·.fst)) (nonstrictposMsg ctorInfo.name)
      let appFn := type.getAppFn
      let appliedField := mkAppN field args
      if let some αmotive := αmotives.lookup appFn then
        let mfieldType ← mkForallFVars args (mkApp αmotive appliedField)
        withLocalDeclD .anonymous mfieldType fun mfield =>
          loop αmotives ctorType (newFields.push mfield) fields
      else if appFn.constName?.isEqSome indVal.name then
        let appArgs := type.getAppArgs
        let params  : Array Expr := appArgs[:indVal.numParams]
        let indices : Array Expr := appArgs[indVal.numParams:]
        let motives := αmotives.map (·.snd)
        let allType := mkAppN allExpr (params ++ motives ++ indices ++ #[appliedField])
        let rfieldType ← mkForallFVars args allType
        withLocalDeclD .anonymous rfieldType fun rfield =>
          loop αmotives ctorType (newFields.push rfield) fields
      else loop αmotives ctorType newFields fields

/--
Given an inductive predicate `I (param : paramType)... : ∀ (index : indexType)..., Prop`
and selected parameters `α...` from `param...`,
create an auxiliary predicate on `I` parametrized over `(motive_α : α → Prop)...`,
which has the following type:
```
I.all : ∀ (param : paramType)... (motive_α : α → Prop)... (index : indexType)...,
        I param... index... → Prop
```
The shape of its constructors are detailed in the doc comment for `buildCtorType`.
-/
def mkIAllDef (indVal : InductiveVal) (αnames : Array Name) (all : Name) : MetaM Declaration := do
  let indType ← forallTelescope indVal.type fun indArgs _ => do
    assert! indArgs.size == indVal.numParams + indVal.numIndices
    let params  : Array Expr := indArgs[:indVal.numParams]
    let indices : Array Expr := indArgs[indVal.numParams:]

    withLocalMotives αnames .zero fun _ motives => do
    let indApp := mkAppN (.const indVal.name (indVal.levelParams.map .param)) indArgs
    let indPred ← mkArrow indApp (.sort .zero)
    let allIndType ←
      withNewBinderInfos (indArgs.map (·.fvarId!, BinderInfo.implicit)) <|
        mkForallFVars (params ++ motives ++ indices) indPred
    let allCtors ← indVal.ctors.mapM (getConstInfoCtor · >>= buildCtorType all αnames indVal)
    pure { name := all, type := allIndType, ctors := allCtors }
  pure <| Declaration.inductDecl
    indVal.levelParams (indVal.numParams + αnames.size) [indType] indVal.isUnsafe

/--
Given a recursor for an inductive type `I` with parameters `param...` and motives `recMotive...`,
along with selected parameters `α...` from `param...` and predicates `(motive_α : α → Prop)...`,
we wish to build the minor premise of the given `minorType`.
We know that the motives will be intantiated to constant functions returning sort `rlvl`,
and the minor premise returns a product that collects
recursive applications and applications of `motive_α`.
That is, it has the shape `λ (field : fieldType)... ↦ prod × ... × prod`,
and if `fieldType` has the shape `∀ (arg : argType)..., appFn appArgs...`,
* When `appFn` is `α`, add `∀ (arg : argType)..., motive_α (field arg...)` to the product;
* When `appFn` is `recMotive`, we know `appFn appArgs...` will be `Sort rlvl`,
  so replace `(field : fieldType)` with `(ih : ∀ (arg : argType)..., Sort rlvl)`,
  and add `∀ (arg : argType)..., ih arg...` to the product;

otherwise, nothing is added to the product.

(N.B. Although minor premises aren't constructors,
we still call their arguments `field`s to distinguish them from *their own* arguments,
and to avoid calling things `argArg`s.)
-/
def buildMinorPremise (rlvl : Level) (αmotives : List (Expr × Expr)) (recMotives : Array Expr)
                      (minorType : Expr) (emsg : Expr → MessageData) : MetaM Expr := do
  forallTelescope minorType fun fields _ => do loop #[] #[] fields.toList
  where
  loop (newFields : Array Expr) (prods : Array Expr) : List Expr → MetaM Expr
  | [] => do mkLambdaFVars newFields (← PProdN.pack rlvl prods)
  | field :: fields => do
    let fieldType ← inferType field
    forallTelescope fieldType fun args type => do
      checkFVars args (αmotives.map (·.snd)) emsg
      let appFn := type.getAppFn
      if let some motive := αmotives.lookup appFn then
        let mprod ← mkForallFVars args (mkApp motive (mkAppN field args))
        loop (newFields.push field) (prods.push mprod) fields
      else if recMotives.contains appFn then
        let ihName ← field.fvarId!.getUserName
        let ihType ← mkForallFVars args (.sort rlvl)
        withLocalDeclD ihName ihType fun ih => do
          let rprod ← mkForallFVars args (mkAppN ih args)
          loop (newFields.push ih) (prods.push rprod) fields
      else loop (newFields.push field) prods fields

/--
Given an inductive type `I (param : paramType)... : ∀ (index : indexType)..., Type`
and selected parameters `α...` from `param...`,
create an auxiliary definition over `I` parametrized over `(motive_α : α → Sort)...`,
which has the following type:
```
I.all : ∀ (param : paramType)... (motive_α : α → Prop)... (index : indexType)...,
        I param... index... → Sort
```
To be able to use motives in arbitrary sorts,
we take advantage of large elimination and build `I.all` using the recursor `I.rec`,
which has the following shape:
```
I.rec : ∀ (param : paramType)...
          (recMotive : ∀ (index : indexType)..., I param... index... → Sort)...
          (minor : minorType)...
          (index : indexType)...,
          (major : I param... index...),
        recMotive index... major
```
Therefore, we keep `param...`, `index...`, and `major`,
while we need to instantiate `recMotive...` and `minor...`.
The recursor's motives are simply constant functions returning `Sort`.
The shape of minor premises are detailed in the doc comment for `buildMinorPremise`.
-/
def mkAllDef (indVal : InductiveVal) (recVal : RecursorVal) (αnames : Array Name) (all : Name) (prop? : Bool) : MetaM Declaration := do
  let allLvlParams@(lvlParam :: lvlParams) := recVal.levelParams
    | throwError "recursor {recVal.name} has no levelParams"
  let lvls : List Level := lvlParams.map .param
  let allLvlParams := if prop? then lvlParams else allLvlParams
  let rlvl : Level := if prop? then 0 else .succ (.param lvlParam)
  let recType := recVal.type.instantiateLevelParams [lvlParam] [rlvl]

  let nParams := indVal.numParams
  let decl ← forallTelescope recType fun refArgs _ => do
    assert! refArgs.size > nParams + recVal.numMotives + recVal.numMinors
    let params   : Array Expr := refArgs[:nParams]
    let rmotives : Array Expr := refArgs[nParams:nParams + recVal.numMotives]
    let minors   : Array Expr := refArgs[nParams + recVal.numMotives:nParams + recVal.numMotives + recVal.numMinors]
    let indices  : Array Expr := refArgs[nParams + recVal.numMotives + recVal.numMinors:refArgs.size - 1]
    let major    : Expr       := refArgs[refArgs.size - 1]!

    withLocalMotives αnames rlvl fun αs motives => do
    let αmotives := List.zip αs.toList motives.toList

    let mut sorts := #[]
    for motive in rmotives do
      let sort ← forallTelescope (← inferType motive) fun targs _ =>
        mkLambdaFVars targs (.sort rlvl)
      sorts := sorts.push sort

    let mut premises := #[]
    for minor in minors, ctor in indVal.ctors do
      let premise ← buildMinorPremise rlvl αmotives rmotives (← inferType minor) (nonstrictposMsg ctor)
      premises := premises.push premise

    let recFn := .const recVal.name (rlvl.succ :: lvls)
    let recApp := mkAppN recFn (params ++ sorts ++ premises ++ indices ++ #[major])
    let allParams := params ++ motives ++ indices ++ #[major]
    let allType ← mkForallFVars allParams (.sort rlvl)
    let allExpr ← mkLambdaFVars allParams recApp
    mkDefinitionValInferrringUnsafe all allLvlParams allType allExpr .abbrev
  pure <| .defnDecl decl

def mkAllInductive (ind : Name) (params : Array Name) : MetaM Unit := do
  let indVal ← getConstInfoInduct ind
  if (← isInductivePredicate ind) then
    addDecl <| ← mkIAllDef indVal params (.str ind "all")
  else
    let .recInfo recVal ← getConstInfo (mkRecName ind) | return
    addDecl <| ← mkAllDef indVal recVal params (.str ind "all")  false
    addDecl <| ← mkAllDef indVal recVal params (.str ind "iall") true

syntax (name := mkAll) "mk_all" (ppSpace ident)+ : attr

initialize Lean.registerBuiltinAttribute {
  name := `mkAll
  descr := "Generate an `all` predicate for an inductive with a strictly positive parameter."
  add := fun decl stx _ => MetaM.run' do
    let ⟨decl, params, stx⟩ ← match stx with
      | `(attr| mk_all $[$params:ident]*) => pure (decl, params, stx)
      | _ => throwError "unrecognized syntax"
    mkAllInductive decl (params.map (·.getId))
}
end MkAll
