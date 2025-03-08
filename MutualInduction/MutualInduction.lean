import Lean.Elab.Tactic.Induction

namespace Lean.Elab.Tactic

structure Goal where
  /-- Syntax object of the target -/
  stx        : Syntax
  name       : Name
  mvarId     : MVarId
  /-- User-facing name of the target -/
  target     : Name
  /-- Target and its indices -/
  targets    : Array Expr
  genFVars   : Array FVarId
  indVal     : InductiveVal
  elimInfo   : Meta.ElimInfo
deriving Inhabited

structure GoalWithMotives extends Goal where
  motive  : Expr
  motives : Array Expr := #[]

structure Alt extends ElimApp.Alt where
  numGenFVars : Nat
deriving Inhabited

/--
Given goals `tag₁ ... tagₙ` each with a variable `x₁ ... xₙ` respectively
which each belong to a different mutual inductive type,
`mutual_induction | tag₁ => x₁ ... | tagₙ => xₙ`
applies mutual induction on each `x` to each goal `tag`.
It produces one goal for each constructor of the mutual inductive types,
in which the target is replaced by a general instance of that constructor
and an inductive hypothesis is added for each mutually recursive argument to the constructor.
Note that exactly one goal and target must be provided for each mutual inductive type.

For example, suppose we have mutual inductive types `Even` and `Odd` with constructors
* `Even.zero : Even`,
* `Even.succ : Odd → Even`, and
* `Odd.succ : Even → Odd`.

Given a goal `even` with hypothesis `e : Even` and type `P e`,
and a goal `odd` with hypothesis `o : Odd` and type `Q o`,
`mutual_induction | even => e | Odd => o` produces three goals
(where names `o`, `e`, `ih` are chosen automatically and not accessible):
* `case even.zero` with state `⊢ P zero`,
* `case even.succ` with state `o : Odd, ih : Q o ⊢ P (Even.succ o)`, and
* `case odd.succ`  with state `e : Even, ih : P e ⊢ Q (Odd.succ o)`.
-/
syntax (name := mutual_induction) "mutual_induction " ("| " (ident <|> "_") " => " term)+ : tactic

/--
Find a metavariable whose name is (a suffix or prefix of) `tag`,
and throw an error if none exists.
This is adapted from `Lean.Elab.Tactic.findTag?`.
-/
def findTag (mvarIds : List MVarId) (tag : Name) : MetaM MVarId := do
  match (← mvarIds.findM? fun mvarId => return tag == (← mvarId.getDecl).userName) with
  | some mvarId => return mvarId
  | none =>
  match (← mvarIds.findM? fun mvarId => return tag.isSuffixOf (← mvarId.getDecl).userName) with
  | some mvarId => return mvarId
  | none =>
  match (← mvarIds.findM? fun mvarId => return tag.isPrefixOf (← mvarId.getDecl).userName) with
  | some mvarId => return mvarId
  | none => throwError m!"goal '{tag}' not found"

/--
Given a list of `targets`, find their transitive dependencies in the local context,
as well as the dependencies of a given expression `e`.
More precisely, we compute:
* `fvarIds`, the free variables whose declarations depend on `targets`,
  but excluding `targets` themselves; and
* `fvarIdDeps`, the free variables depended upon by the declarations of `fvarIds` and by `e`,
  again excluding `targets` themselves.

For example, given the context and goal:
```
  P : ∀ n, Fin n → Prop
  n m : Nat
  q : n = m
  f : Fin n
  p : P n f
  -------------
  ⊢ P m (q ▸ f)
```
If `f` and `n` are the targets, then `fvarIds` contains `p` and `q`,
and `fvarIdDeps` contains `m`, since `q` depends on it.
If `P m (q ▸ f)` is the additional expression,
then `fvarIdDeps` would also contain `P`.

Precondition: `targets` must be free variables.
Postcondition: The resulting array is sorted in order of declaration.
-/
def getFVarsToGeneralize (targets : Array Expr) (e : Expr) : MetaM (Array FVarId) := do
  let targetFVars := targets.map (·.fvarId!)
  let fvarIds ← Meta.getFVarsToGeneralize targets
  let mut s := collectFVars {} (← instantiateMVars e)
  for fvarId in fvarIds do
    let decl ← fvarId.getDecl
    s := collectFVars s (← instantiateMVars decl.type)
    if let some val := decl.value? then
      s := collectFVars s (← instantiateMVars val)
  let fvarIdDeps := s.fvarIds.filter (not ∘ targetFVars.contains)
  let fvarIds ← Meta.sortFVarIds (fvarIds ++ fvarIdDeps)
  return fvarIds

/--
Given all goals of the mutual induction, check that they exactly cover the inductive types:
* The targets must all belong to inductive types in the same mutual declaration;
* The targets must each belong to a different inductive type; and
* The targets must belong to all of the mutual inductive types.

Precondition: There must exist at least one goal.
-/
def checkTargets (goals : Array Goal) : MetaM Unit := do
  for i in [0:goals.size] do
    for j in [0:i] do
      let goal1 := goals[j]!
      let goal2 := goals[i]!
      unless goal1.indVal.all.contains goal2.indVal.name do
        Meta.throwTacticEx `mutual_induction goal1.mvarId
          m!"targets do not belong to mutual inductive types: \
             {goal1.target} is in {goal1.indVal.name}, \
             while {goal2.target} is in {goal2.indVal.name}"
      if goal1.indVal.name == goal2.indVal.name then
        Meta.throwTacticEx `mutual_induction goal1.mvarId
          m!"duplicate target inductive types: \
             {goal1.target} and {goal2.target} are both in {goal1.indVal.name}"
  let allIndNames := goals[0]!.indVal.all
  let targetIndNames := goals.map (·.indVal.name)
  let mut missingIndNames : Array Name := #[]
  for indName in allIndNames do
    unless targetIndNames.contains indName do
    missingIndNames := missingIndNames.push indName
  unless missingIndNames.isEmpty do
    Meta.throwTacticEx `mutual_induction goals[0]!.mvarId
      m!"missing targets for mutual inductive types: {missingIndNames}"

/--
Compute all motives for all goals,
in each goal abstracting over the goal's targets
and generalizing over the goal's free variables,
unless the variable is free in all goals,
preventing unnecessary generalization.

For example, given the following two goals:
```
case goal1
  n m : Nat
  e : n = m
  en : Even n
  -----------
  ⊢ Even m

case goal2
  n m : Nat
  e : n = m
  on : Odd n
  ----------
  ⊢ Odd m
```
If `n` and `e` are shared between the two goals, then the motives are:
```
  motive_1 : λ n (en : Even n) ↦ Even m
  motive_2 : λ n (on : Odd n)  ↦ Odd m
```
But if they are not shared, then the motives are:
```
  motive_1 : λ n (en : Even n) ↦ ∀ m, n = m → Even m
  motive_2 : λ n (on : Odd n)  ↦ ∀ m, n = m → Odd m
```

Postconditions:
* Each of the `n` goals has `n - 1` motives;
* The motives in each goal are sorted declaration order of the inductives they apply to; and
* The goals themselves are sorted by their motives in the same order.
-/
def addMotives (gs : Array Goal) : MetaM (Array GoalWithMotives) := do
  let gs ← gs.mapM filterGenFVars
  let gs ← gs.mapM addMotive
  let gs := gs.qsort (·.elimInfo.motivePos < ·.elimInfo.motivePos)
  return gs.map (addMotives gs)
where
  addMotives (goals : Array GoalWithMotives) (goal : GoalWithMotives) : GoalWithMotives :=
    let goals := goals.filter (·.elimInfo.motivePos != goal.elimInfo.motivePos)
    {goal with
      motives := goals.map (·.motive)
      elimInfo := {goal.elimInfo with
        targetsPos := goals.map (·.elimInfo.motivePos)
                   ++ goal.elimInfo.targetsPos}}
  addMotive (g : Goal) : MetaM GoalWithMotives := do
    g.mvarId.withContext do
    let ⟨genFVars, goal⟩ ← g.mvarId.revert g.genFVars
    goal.withContext do
    let goalType ← MetavarDecl.type <$> goal.getDecl
    let motive ← Meta.mkLambdaFVars g.targets goalType
    return {g with mvarId := goal, genFVars, motive}
  filterGenFVars (g : Goal) : MetaM Goal := do
    let genFVars ← g.genFVars.filterM notFreeInAnyGoal
    return {g with genFVars}
  notFreeInAnyGoal (fvarId : FVarId) : MetaM Bool :=
    gs.anyM (notFreeInGoal fvarId)
  notFreeInGoal (fvarId : FVarId) (g : Goal) : MetaM Bool :=
    g.mvarId.withContext do
      let lctx ← getLCtx
      return !lctx.contains fvarId

/--
Each application of mutual recursors produces exactly the same new subgoals
each corresponding to a constructor of one of the mutual inductive types;
`alts` contains these subgoals for each recursor application.
Therefore, only one sequence of subgoals needs to be solved,
and every other sequence can be pointwise assigned the same solution.
The sequence we pick out should be the subgoals that prove the motive of its recursor,
since it informs which parent case name it's associated with.
The case names are in an association list `tags` that map from the inductive types' names.

Preconditions:
* There must exist at least one sequence of subgoals; and
* All sequences of subgoals must have the same length and pointwise have the same type.
-/
def deduplicate (tags : Array (Name × Name)) (alts : Array (Array Alt)) : MetaM (Array Alt) := do
  let mut deduped := alts[0]!
  -- find the canonical alternatives that prove the motive
  for alt in alts do
    for i in [0:alt.size] do
      if alt[i]!.info.provesMotive then
        deduped := deduped.set! i alt[i]!
  -- assign identical alternatives to canonical alternative
  for alt in alts do
    for i in [0:alt.size] do
      let deAlt := deduped[i]!.mvarId
      let otherAlt := alt[i]!.mvarId
      unless deAlt == otherAlt do
      let altExpectedType ← Meta.inferType (.mvar deAlt)
      let altType ← Meta.inferType (.mvar otherAlt)
      if ← Meta.isDefEqGuarded altExpectedType altType then
        otherAlt.assign (.mvar deAlt)
  -- ensure root of user-facing name corresponds to the original subgoal name
  for alt in deduped do
    let mctx ← getMCtx
    let some name := altName alt | continue
    let mctx := MetavarContext.setMVarUserName mctx alt.mvarId name
    setMCtx mctx
  return deduped
where
  altName (alt : Alt) : Option Name :=
    match alt.info.declName? with
    | some (.str ind cstr) => do
      let tag ← tags.toList.lookup ind
      return .str tag cstr
    | _ => none

/--
Given a single goal name and target in that goal of the form
```
syntax mutualInductionTarget := ("| " ident " => " term)
```
produce all the information we can glean without considering the other mutual goals:
the target and its indices, its inductive type,
the goal and its the free variables to generalize,
and information about the eliminator to be applied.
-/
def getSubgoal (stx : Syntax) : TacticM Goal :=
  match Syntax.getKind stx, stx.getArgs with
  | `group, #[_, tag, _, targetName] => do
    let goals ← getUnsolvedGoals
    let goal ← findTag goals tag.getId
    goal.withContext do
    let target ← elabTerm targetName none
    let indVal ← getInductiveVal goal target
    let elimInfo ← Meta.getElimInfo (mkRecName indVal.name) indVal.name
    let ⟨goal, target⟩ ← generalizeTarget goal target
    goal.withContext do
    let targetUserName ← target.fvarId!.getUserName
    let targets ← Meta.addImplicitTargets elimInfo #[target]
    evalInduction.checkTargets targets
    let goalType ← MetavarDecl.type <$> goal.getDecl
    let genFVars ← getFVarsToGeneralize targets goalType
    return ⟨targetName, tag.getId, goal, targetUserName, targets, genFVars, indVal, elimInfo⟩
  | _, _ => throwError m!"failed to parse {stx}"
where
  /--
  Adapted from `Lean.Elab.Tactic.getInductiveValFromMajor`,
  which for some reason works in the context of the main goal,
  not in the current context, so using it directly would not find the target,
  which only exists in the context of the subgoal.
  -/
  getInductiveVal (mvarId : MVarId) (target : Expr) : MetaM InductiveVal :=
    mvarId.withContext do
      let targetType ← Meta.inferType target
      let targetType ← Meta.whnf targetType
      matchConstInduct targetType.getAppFn
        (fun _ => Meta.throwTacticEx `mutual_induction mvarId
          m!"target is not an inductive type{indentExpr targetType}")
        (fun val _ => pure val)
  /--
  Adapted from `Lean.Elab.Tactic.generalizeTargets`,
  which for some reason also works in the context of the main goal.
  -/
  generalizeTarget (mvarId : MVarId) (target : Expr) : TacticM (MVarId × Expr) := do
    mvarId.withContext do
      let generalize? ← do
        if target.isFVar then target.fvarId!.isLetVar else pure true
      if generalize? then
        let ⟨#[target], mvarId⟩ ← mvarId.generalize #[{ expr := target }]
          | Meta.throwTacticEx `mutual_induction mvarId
              m!"failed to generalize target{indentExpr target}"
        return ⟨mvarId, .fvar target⟩
      else return ⟨mvarId, target⟩

/--
Apply the eliminator in a goal `g` and return the new metavariables to solve,
each corresponding to the constructor cases of the eliminator.
The new metavariables are *not* yet added to the list of goals.
The motives from the other mutual goals are considered as targets.

Preconditions:
* `g.motives` contains the other motives in declaration order of the inductives they apply to;
* `g.elimInfo.elimExpr` is an eliminator that proves the motive `g.motive`
  and takes all motives in the same declaration order; and
* `g.elimInfo.targetsPos` also contains the positions of the other motives in the eliminator.
-/
def evalSubgoal (g : GoalWithMotives) : TacticM (Array Alt) :=
  g.mvarId.withContext do
    -- instantiate eliminator
    let result ← withRef g.stx do
      ElimApp.mkElimApp g.elimInfo (g.motives ++ g.targets) g.mvarId.name
    -- assign current motive
    let motiverInferredType ← Meta.inferType g.motive
    let motiveType ← Meta.inferType (.mvar result.motive)
    unless (← Meta.isDefEqGuarded motiverInferredType motiveType) do
      Meta.throwTacticEx `mutual_induction g.mvarId
        m!"type mismatch when assigning motive{indentExpr g.motive}\n\
           {← Meta.mkHasTypeButIsExpectedMsg motiverInferredType motiveType}"
    result.motive.assign g.motive
    -- apply eliminator
    g.mvarId.assign result.elimApp
    -- return subgoals
    let targetFVars := g.targets.map (·.fvarId!)
    let alts ← result.alts.mapM (clearTargets targetFVars)
    appendGoals result.others.toList
    return alts.map ({· with numGenFVars := g.genFVars.size})
where
  clearTargets (mvarIds : Array FVarId) (alt : ElimApp.Alt) : TacticM ElimApp.Alt := do
    let mvarId ← alt.mvarId.tryClearMany mvarIds
    return {alt with mvarId := mvarId}

/--
When evaluating the mutual induction tactic,
the eliminators of each goal are computed independently first.
Next, the motives are computed in tandem,
since each one needs to be generalized over free variables missing in the others.
Only then knowing the motives for each goal can we specialize
each eliminator with all motives and apply it to their goals.
The mutual eliminators produce identical subgoals,
which we deduplicate so that the user ony needs to solve one set of them.
-/
@[tactic mutual_induction]
def evalMutualInduction : Tactic := λ stx ↦ do
  let subgoals ← stx[1].getArgs.mapM getSubgoal
  checkTargets subgoals
  let tags := subgoals.map (λ goal ↦ ⟨goal.indVal.name, goal.name⟩)
  let subgoals ← addMotives subgoals
  let subgoals ← subgoals.mapM evalSubgoal
  let subgoals ← deduplicate tags subgoals
  for subgoal in subgoals do
    let ⟨_, mvarId⟩ ← subgoal.mvarId.introN subgoal.info.numFields
    let ⟨_, mvarId⟩ ← mvarId.introNP subgoal.numGenFVars
    appendGoals [mvarId]

end Tactic
