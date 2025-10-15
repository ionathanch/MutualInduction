import Lean.Elab.Tactic.Induction

-- Why is this not in Lean.Expr?
def Lean.Expr.mvarId? : Expr → Option MVarId
  | .mvar n => some n
  | _      => none

namespace Lean.Elab.Tactic
open Meta

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
  elimInfo   : ElimInfo
deriving Inhabited

structure GoalWithMotives extends Goal where
  motive  : Expr
  motives : Array Expr := #[]

structure Alt extends ElimApp.Alt where
  numGenFVars : Nat := 0
  trivial : Bool := false
deriving Inhabited

/--
Given `n` goals to be solved, each with a variable `x₁ ... xₙ` respectively
which each belong to a different mutual inductive type,
`mutual_induction x₁, ..., xₙ`
applies mutual induction on each `x` to each goal.
It produces one goal for each constructor of the mutual inductive types,
in which the target is replaced by a general instance of that constructor
and an inductive hypothesis is added for each mutually recursive argument to the constructor.
Note that exactly one goal and target must be provided for each mutual inductive type.

* `mutual_induction x₁, ..., xₙ using r₁, ..., rₙ`
  allows specifying the principles of induction for each of the `n` goals, respectively.
  There must be exactly as many eliminators provided as there are goals targeted.
  Here, each `rᵢ` must be a term whose result type has the form `Cᵢ tᵢ...`,
  where `Cᵢ` is a bound variable representing the motive of the `i`th goal
  and `tᵢ...` is a (possibly empty) sequence of bound variables.
  Furthermore, every `rᵢ` must quantify over
  exactly the same motives `C₁ ... Cₙ` in exactly the same order.
* `mutual_induction x₁, ..., xₙ generalizing z₁ ... zₘ`,
  where `z₁ ... zₘ` are variables in the contexts of all `n` goals,
  generalizes over `z₁ ... zₘ` before applying the induction,
  but then reintroduces them in each new goal produced.
  The net effect is that each inductive hypothesis is generalized.

As an example, suppose we have mutual inductive types `Even` and `Odd` with constructors
* `Even.zero : Even`,
* `Even.succ : Odd → Even`, and
* `Odd.succ : Even → Odd`.

Given a goal `even` with hypothesis `e : Even` and type `P e`,
and a goal `odd` with hypothesis `o : Odd` and type `Q o`,
`mutual_induction e, o` produces three goals
(where names `o`, `e`, `ih` are chosen automatically and not accessible):
* `case even.zero` with state `⊢ P zero`,
* `case even.succ` with state `o : Odd, ih : Q o ⊢ P (Even.succ o)`, and
* `case odd.succ`  with state `e : Even, ih : P e ⊢ Q (Odd.succ o)`.
-/
syntax (name := mutual_induction)
  "mutual_induction " term,+
    (" using" term,+)?
    (" generalizing" (ppSpace colGt term:max)+)?
  : tactic

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
If custom arguments are provided,
ensure there are exactly as many as there are targets,
returning a list of optional arguments the length of the number of targets.
-/
def countArgs {α} (mvarId : MVarId) (argName : Name) (numTargets : Nat) (args? : Option (Array α)) : MetaM (Array (Option α)) := do
  let some args := args?
    | return Array.replicate numTargets none
  unless args.isEmpty || args.size == numTargets do
    throwTacticEx `mutual_induction mvarId
      m!"incorrect number of {argName} provided: \
         expected {numTargets}, but got {args.size}"
  return args.map some

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
  return fvarIds ++ fvarIdDeps

/--
Given all goals of the mutual induction, check that they exactly cover the inductive types:
* The targets must all belong to inductive types in the same mutual declaration;
* The targets must each belong to a different inductive type; and
* [Deprecated] The targets must belong to all of the mutual inductive types.

Precondition: There must exist at least one goal.
-/
def checkTargets (goals : Array Goal) : MetaM Unit := do
  for i in [0:goals.size] do
    for j in [0:i] do
      let goal1 := goals[j]!
      let goal2 := goals[i]!
      unless goal1.indVal.all.contains goal2.indVal.name do
        throwTacticEx `mutual_induction goal1.mvarId
          m!"targets do not belong to mutual inductive types: \
             {goal1.target} is in {goal1.indVal.name}, \
             while {goal2.target} is in {goal2.indVal.name}"
      if goal1.indVal.name == goal2.indVal.name then
        throwTacticEx `mutual_induction goal1.mvarId
          m!"duplicate target inductive types: \
             {goal1.target} and {goal2.target} are both in {goal1.indVal.name}"
  /- No longer requiring coverage of all inductives -/
  -- let allIndNames := goals[0]!.indVal.all
  -- let targetIndNames := goals.map (·.indVal.name)
  -- let mut missingIndNames : Array Name := #[]
  -- for indName in allIndNames do
  --   unless targetIndNames.contains indName do
  --   missingIndNames := missingIndNames.push indName
  -- unless missingIndNames.isEmpty do
  --   throwTacticEx `mutual_induction goals[0]!.mvarId
  --     m!"missing targets for mutual inductive types: {missingIndNames}"

/--
Ensure that all given "free" variables are declared in the contexts of each goal.
(They're not really "free" if they're bound in the context, are they?)
-/
def checkFVars (goals : Array Goal) (idents : Array Syntax) : TermElabM Unit := do
  for goal in goals do
    for ident in idents do
      goal.mvarId.withContext do
      if let none ← Term.resolveId? ident then
        throwTacticEx `mutual_induction goal.mvarId
          m!"unknown identifier '{ident}' in goal '{goal.name}'"

/--
Compute all motives for all goals,
in each goal abstracting over the goal's targets
and generalizing over the goal's free variables,
unless the variable is free in all goals,
preventing unnecessary generalization,
except when explicitly generalized by the user.

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
If `m` is shared between the two goals, then the motives are:
```
  motive_1 : λ n (en : Even n) ↦ n = m → Even m
  motive_2 : λ n (on : Odd n)  ↦ n = m → Odd m
```
But if they are not shared, or if `m` is explicitly generalized, then the motives are:
```
  motive_1 : λ n (en : Even n) ↦ ∀ m, n = m → Even m
  motive_2 : λ n (on : Odd n)  ↦ ∀ m, n = m → Odd m
```

Preconditions:
* The motives that each goal's eliminator quantifies over are exactly in the same order.

Postconditions:
* Each of the `n` goals has `n - 1` motives;
* The motives in each goal are sorted by the order its eliminator quantifies over them; and
* The goals themselves are sorted by their motives in the same order.
-/
def addMotives (gs : Array Goal) (userFVars : Array FVarId): MetaM (Array GoalWithMotives) := do
  let gs ← gs.mapM filterGenFVars
  let gs ← gs.mapM genUserFVars
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
  addMotive (g : Goal) : MetaM GoalWithMotives :=
    g.mvarId.withContext do
    let ⟨genFVars, goal⟩ ← sortFVarIds g.genFVars >>= g.mvarId.revert
    goal.withContext do
    let goalType ← MetavarDecl.type <$> goal.getDecl
    let motive ← mkLambdaFVars g.targets goalType
    return {g with mvarId := goal, genFVars, motive}
  genUserFVars (g : Goal) : MetaM Goal :=
    g.mvarId.withContext do
    let forbidden ← mkGeneralizationForbiddenSet g.targets
    for userFVarId in userFVars do
      if forbidden.contains userFVarId then
        throwError "variable cannot be generalized because target depends on it{indentExpr (mkFVar userFVarId)}"
      if g.genFVars.contains userFVarId then
        throwError "unnecessary 'generalizing' argument, variable '{mkFVar userFVarId}' is generalized automatically"
    pure {g with genFVars := userFVars ++ g.genFVars}
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
The case names are in an association list `tags` that map from the inductive types' names,
defaulting to the provided main goal's `tag`.

Preconditions:
* There must exist at least one sequence of subgoals; and
* All sequences of subgoals must have the same length and pointwise have the same type.
-/
def deduplicate (tag : Name) (tags : Array (Name × Name)) (alts : Array (Array Alt)) : MetaM (Array Alt) := do
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
      let altExpectedType ← inferType (.mvar deAlt)
      let altType ← inferType (.mvar otherAlt)
      if ← isDefEqGuarded altExpectedType altType then
        otherAlt.assign (.mvar deAlt)
  -- ensure root of user-facing name corresponds to the original subgoal name
  for alt in deduped do
    let .str ind cstr := alt.info.declName?.getD (← alt.mvarId.getTag) | continue
    let tag := (tags.toList.lookup ind).getD tag
    alt.mvarId.setTag <| .str tag cstr
  return deduped

/--
Given a goal and a target in that goal,
produce all the information we can glean without considering the other mutual goals:
the target and its indices, its inductive type,
the goal and its the free variables to generalize,
and information about the eliminator to be applied.
-/
def getSubgoal (stxgoal : Syntax × Option Syntax × MVarId) : TacticM Goal :=
  let ⟨targetName, elim?, goal⟩ := stxgoal
  goal.withContext do
  let target ← elabTerm targetName none
  let indVal ← getInductiveVal goal target
  let elimInfo ← do
    let some elim := elim?
      | getElimInfo (mkRecName indVal.name) indVal.name
    getElimExprInfo (← elabTermForElim elim) indVal.name
  let ⟨goal, target⟩ ← generalizeTarget goal target
  goal.withContext do
  let targetUserName ← target.fvarId!.getUserName
  let targets ← addImplicitTargets elimInfo #[target]
  checkInductionTargets targets
  let goalType ← MetavarDecl.type <$> goal.getDecl
  let genFVars ← getFVarsToGeneralize targets goalType
  return ⟨targetName, (← goal.getDecl).userName, goal, targetUserName, targets, genFVars, indVal, elimInfo⟩
where
  /--
  Adapted from `Lean.Elab.Tactic.getInductiveValFromMajor`,
  which for some reason works in the context of the main goal,
  not in the current context, so using it directly would not find the target,
  which only exists in the context of the subgoal.
  -/
  getInductiveVal (mvarId : MVarId) (target : Expr) : MetaM InductiveVal :=
    mvarId.withContext do
      let targetType ← inferType target
      let targetType ← whnf targetType
      matchConstInduct targetType.getAppFn
        (fun _ => throwTacticEx `mutual_induction mvarId
          m!"target is not an inductive type{indentExpr targetType}")
        (fun val _ => pure val)
  /--
  Copied from `Lean.Elab.Tactic.elabTermForElim`, which is private.
  -/
  elabTermForElim (stx : Syntax) : TermElabM Expr := do
    if stx.isIdent then
      if let some e ← Term.resolveId? stx (withInfo := true) then
        return e
    Term.withoutErrToSorry <| Term.withoutHeedElabAsElim do
      let e ← Term.elabTerm stx none (implicitLambda := false)
      Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
      let e ← instantiateMVars e
      let e := e.eta
      if e.hasMVar then
        let r ← abstractMVars (levels := false) e
        return r.expr
      else
        return e
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
          | throwTacticEx `mutual_induction mvarId
              m!"failed to generalize target{indentExpr target}"
        return ⟨mvarId, .fvar target⟩
      else return ⟨mvarId, target⟩

/--
Apply the eliminator in a goal `g` and return the new metavariables to solve,
each corresponding to the constructor cases of the eliminator.
The new metavariables are *not* yet added to the list of goals.
The motives from the other mutual goals are considered as targets.
If a motive is missing, assign it the trivial predicate returning `PUnit`.

Preconditions:
* `g.motives` contains the other motives in the order its eliminator quantifies over them;
* `g.elimInfo.elimExpr` is an eliminator that proves the motive `g.motive`; and
* `g.elimInfo.targetsPos` also contains the positions of the other motives in the eliminator.
-/
def evalSubgoal (g : GoalWithMotives) : TacticM (Array Alt) :=
  g.mvarId.withContext do
    -- instantiate eliminator
    let result ← withRef g.stx do
      ElimApp.mkElimApp g.elimInfo (g.motives ++ g.targets) g.mvarId.name
    -- assign current motive
    let motiverInferredType ← inferType g.motive
    let motiveType ← inferType (.mvar result.motive)
    unless (← isDefEqGuarded motiverInferredType motiveType) do
      throwTacticEx `mutual_induction g.mvarId
        m!"type mismatch when assigning motive{indentExpr g.motive}\n\
           {← mkHasTypeButIsExpectedMsg motiverInferredType motiveType}"
    result.motive.assign g.motive
    -- apply eliminator
    let newGoals := result.alts.map (·.mvarId) ++ result.others
    let elimApp ← instantiateMVars result.elimApp
    let unsolvedMotives ← appendMotives elimApp.getAppArgs newGoals
    g.mvarId.assign elimApp
    -- return subgoals
    let targetFVars := g.targets.map (·.fvarId!)
    let alts ← result.alts.mapM (clearTargets targetFVars)
    appendGoals result.others.toList
    alts.mapM (addNumGenFVars unsolvedMotives)
where
  addNumGenFVars (unsolvedMotives : Array MVarId) (alt : ElimApp.Alt) : TacticM Alt := do
    let altType ← inferType (.mvar alt.mvarId)
    let altHead := altType.getForallBody.getAppFn
    let trivial :=
      if let some altHeadMVar := altHead.mvarId? then
        unsolvedMotives.contains altHeadMVar
      else false
    if alt.info.provesMotive
    then return {alt with trivial, numGenFVars := g.genFVars.size}
    else return {alt with trivial}
  appendMotives (es : Array Expr) (altMVarIds : Array MVarId) : TacticM (Array MVarId) := do
    let mut unsolvedMotives : Array MVarId := #[]
    for e in es,
        name in g.elimInfo.elimType.getForallBinderNames do
      let some mvarId := e.mvarId? | continue
      unless altMVarIds.contains mvarId do
        mvarId.setTag name
        unsolvedMotives := unsolvedMotives.push mvarId
    -- add motives as goals instead of marking them as trivial
    /- pushGoals unsolvedMotives.toList
       return #[] -/
    unsolvedMotives.forM trivialMotive
    return unsolvedMotives
  trivialMotive (mvarId : MVarId) : TacticM Unit := do
    let motiveType ← inferType (.mvar mvarId)
    forallTelescope motiveType fun args bodyType => do
      let trivial ← mkLambdaFVars args (.const `PUnit [bodyType.sortLevel!])
      mvarId.assign trivial
  clearTargets (mvarIds : Array FVarId)  (alt : ElimApp.Alt) : TacticM ElimApp.Alt := do
    let mvarId ← alt.mvarId.tryClearMany mvarIds
    return {alt with mvarId}

/--
Intro the induction hypotheses of the goal, clearing away useless `PUnit`s,
along with generalized variables.
If the goal itself is trivial because its motive was instantiated as `PUnit`,
solve the goal by `constructor`.
Otherwise, add the goal to the current list of goals.
-/
def addSubgoal (subgoal : Alt) : TacticM Unit := do
  let ⟨ihs, mvarId⟩ ← subgoal.mvarId.introN subgoal.info.numFields
    let ⟨_, mvarId⟩ ← mvarId.introNP subgoal.numGenFVars
    let punits ← mvarId.withContext <| ihs.filterM isPUnit
    let mvarId ← mvarId.tryClearMany punits
    if subgoal.trivial then
      let mvarIds ← mvarId.constructor
      unless mvarIds.isEmpty do
        throwTacticEx `mutual_induction mvarId
          m!"could not solve generated subgoal {subgoal.name}"
    else pushGoal mvarId
  where
    isPUnit (ih : FVarId) : TacticM Bool := do
      let ihType ← ih.getType >>= instantiateMVars
      let ihType ← whnf ihType
      return ihType.isConstOf `PUnit

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
  let tag ← getMainGoal >>= (·.getTag)
  let ⟨targetNames, elims, genFVarNames⟩ := parse stx
  let elims ← countArgs (← getMainGoal) `eliminators targetNames.size elims
  let stxgoals := Array.zip targetNames (Array.zip elims (← getUnsolvedGoals).toArray)
  let subgoals ← stxgoals.mapM getSubgoal
  checkTargets subgoals
  checkFVars subgoals genFVarNames
  let genFVars ← getFVarIds genFVarNames
  let tags := subgoals.map (λ goal ↦ ⟨goal.indVal.name, goal.name⟩)
  let subgoals ← addMotives subgoals genFVars
  let subgoals ← subgoals.mapM evalSubgoal
  let subgoals ← deduplicate tag tags subgoals
  for subgoal in subgoals.reverse do addSubgoal subgoal
  where
    -- #["mutual_induction", #[x₁, ..., xₙ], #["using", #[z₁, ..., zₙ]]?, #["generalizing", #[y₁, ..., yₘ]]?]
    parse (stx : Syntax) : Array Syntax × Option (Array Syntax) × Array Syntax :=
      let targets := stx[1].getSepArgs
      let elims? := stx[2].getArgs
      let elims := match elims? with
        | #[_, elims] => some elims.getSepArgs
        | _ => none
      let genVars? := stx[3].getArgs
      let genVars := match genVars? with
        | #[_, genVars] => genVars.getArgs
        | _ => #[]
      ⟨stx[1].getSepArgs, elims, genVars⟩

end Tactic
