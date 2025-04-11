import CBPV.Syntax

open ValType ComType Val Com

section
set_option hygiene false
local notation:40 v:41 "⤳" w:41 => SRVal v w
local notation:40 m:41 "⤳" n:41 => SRCom m n

mutual
inductive SNeVal : Val → Prop where
  | var {x} : SNeVal (var x)

inductive SNeCom : Com → Prop where
  | force {v} : SNeVal v → SNeCom (force v)
  | app {m v} : SNeCom m → SNVal v → SNeCom (app m v)
  | letin {m n} : SNeCom m → SNCom n → SNeCom (letin m n)

inductive SNVal : Val → Prop where
  | unit : SNVal unit
  | thunk {m} : SNCom m → SNVal (thunk m)
  | ne {v} : SNeVal v → SNVal v
  | red {v w : Val} : v ⤳ w → SNVal w → SNVal v

inductive SNCom : Com → Prop where
  | lam {m} : SNCom m → SNCom (lam m)
  | ret {v} : SNVal v → SNCom (ret v)
  | ne {m} : SNeCom m → SNCom m
  | red {m n : Com} : m ⤳ n → SNCom n → SNCom m

inductive SRVal : Val → Val → Prop where
  | thunk {m n : Com} : m ⤳ n → thunk m ⤳ thunk n

inductive SRCom : Com → Com → Prop where
  | thunk {m} : force (thunk m) ⤳ m
  | lam {m : Com} {v} : SNVal v → app (lam m) v ⤳ m⦃v⦄
  | ret {v m} : SNVal v → letin (ret v) m ⤳ m⦃v⦄
  | force {v w : Val} : v ⤳ w → force v ⤳ force w
  | app {m n : Com} {v} : m ⤳ n → app m v ⤳ app n v
  | letin {m m' n : Com} : m ⤳ m' → letin m n ⤳ letin m' n
end
end

notation:40 v:41 "⤳" w:41 => SRVal v w
notation:40 m:41 "⤳" n:41 => SRCom m n

-- Inversion on strong normalization of `force`
theorem SNCom.force_inv {v : Val} (h : SNCom (force v)) : SNVal v := by
  generalize e : force v = m at h
  mutual_induction h generalizing v
  case motive_1 => exact λ _ _ ↦ True
  case motive_2 => exact λ _ _ ↦ True
  case motive_3 => exact λ _ _ ↦ True
  case motive_5 => exact λ _ _ _ ↦ True
  case motive_6 => exact λ _ _ _ ↦ True
  all_goals first | simp | contradiction | subst e
  case ne sne => cases sne with | _ snev => exact .ne snev
  case red sn _ ih r =>
    cases r
    case thunk => exact .thunk sn
    case force r => exact .red r (ih rfl)

/-*---------------------------------------
  Transitive closure of strong reduction
---------------------------------------*-/

section
set_option hygiene false
local notation:40 v:41 "⤳⋆" w:41 => SRVals v w
inductive SRVals : Val → Val → Prop where
  | refl {v : Val} : v ⤳⋆ v
  | trans {u v w : Val} : u ⤳ v → v ⤳⋆ w → u ⤳⋆ w

local notation:40 m:41 "⤳⋆" n:41 => SRComs m n
inductive SRComs : Com → Com → Prop where
  | refl {m : Com} : m ⤳⋆ m
  | trans {k m n : Com} : k ⤳ m → m ⤳⋆ n → k ⤳⋆ n
end

notation:40 v:41 "⤳⋆" w:41 => SRVals v w
notation:40 m:41 "⤳⋆" n:41 => SRComs m n

@[refl] def SRVals.rfl {v} := @SRVals.refl v
@[refl] def SRComs.rfl {m} := @SRComs.refl m

def SRVals.once {u v : Val} (r : u ⤳ v) : u ⤳⋆ v := .trans r .refl
def SRComs.once {m n : Com} (r : m ⤳ n) : m ⤳⋆ n := .trans r .refl

theorem SRVals.trans' {u v w : Val} (r₁ : u ⤳⋆ v) (r₂ : v ⤳⋆ w) : u ⤳⋆ w := by
  induction r₁ generalizing w
  case refl => exact r₂
  case trans r _ ih => exact .trans r (ih r₂)

theorem SRComs.trans' {k m n : Com} (r₁ : k ⤳⋆ m) (r₂ : m ⤳⋆ n) : k ⤳⋆ n := by
  induction r₁ generalizing n
  case refl => exact r₂
  case trans r _ ih => exact .trans r (ih r₂)

instance : Trans SRVals SRVals SRVals where
  trans := SRVals.trans'

instance : Trans SRComs SRComs SRComs where
  trans := SRComs.trans'

/-*--------------------------------
  Congruence and inversion lemmas
  on strong reduction as needed
--------------------------------*-/

theorem SRComs.force {v w : Val} (r : v ⤳⋆ w) : force v ⤳⋆ force w := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.force r₁) r₂

theorem SRComs.app {m n : Com} {v} (r : m ⤳⋆ n) : app m v ⤳⋆ app n v := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.app r₁) r₂

theorem SRComs.letin {m m' n : Com} (r : m ⤳⋆ m') : letin m n ⤳⋆ letin m' n := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.letin r₁) r₂

theorem SRVals.unit_inv {v : Val} (r : v ⤳⋆ .unit) : v = .unit := by
  generalize e : Val.unit = w at r
  induction r
  case refl => rfl
  case trans r _ ih => rw [ih e] at r; subst e; cases r

/-*--------------------------------------
  Backward closure wrt strong reduction
--------------------------------------*-/

theorem SRComs.closure {m n : Com} (r : m ⤳⋆ n) (h : SNCom n) : SNCom m := by
  induction r
  case refl => assumption
  case trans r _ ih => exact .red r (ih h)

theorem SRVals.closure {v w : Val} (r : v ⤳⋆ w) (h : SNeVal w) : SNeVal v := by
  cases h
  generalize e : Val.var _ = w at r
  induction r
  case refl => subst e; constructor
  case trans r _ ih => cases ih e; cases r

/-*--------------------------------
  Antirenaming and extensionality
--------------------------------*-/

theorem antirenaming {ξ} :
  (∀ {v}, SNeVal (renameVal ξ v) → SNeVal v) ∧
  (∀ {m}, SNeCom (renameCom ξ m) → SNeCom m) ∧
  (∀ {v}, SNVal  (renameVal ξ v) → SNVal v)  ∧
  (∀ {m}, SNCom  (renameCom ξ m) → SNCom m)  ∧
  (∀ {v w}, SRVal (renameVal ξ v) w → ∃ w', w = renameVal ξ w' ∧ SRVal v w') ∧
  (∀ {m n}, SRCom (renameCom ξ m) n → ∃ n', n = renameCom ξ n' ∧ SRCom m n') := by
  refine ⟨λ snev ↦ ?sneval, λ snem ↦ ?snecom,
          λ snv  ↦ ?snval,  λ snm  ↦ ?sncom,
          λ r    ↦ ?srval,  λ r    ↦ ?srcom⟩
  case' srcom  => generalize e : renameCom ξ _ = m' at r
  case' srval  => generalize e : renameVal ξ _ = v' at r
  case' sncom  => generalize e : renameCom ξ _ = m' at snm
  case' snval  => generalize e : renameVal ξ _ = v' at snv
  case' snecom => generalize e : renameCom ξ _ = m' at snem
  case' sneval => generalize e : renameVal ξ _ = v' at snev
  mutual_induction snev, snem, snv, snm, r, r generalizing ξ
  case sneval.var v => cases v <;> injection e; constructor
  case snecom.force ih m =>
    cases m <;> try contradiction
    injection e with e
    exact .force (ih e)
  case snecom.app ihm ihv m =>
    cases m <;> try contradiction
    injection e with em ev
    exact .app (ihm em) (ihv ev)
  case snecom.letin ihm ihn m =>
    cases m <;> try contradiction
    injection e with em en
    exact .letin (ihm em) (ihn en)
  case snval.unit v => cases v <;> injection e; constructor
  case snval.thunk ih v =>
    cases v <;> try contradiction
    injection e with e
    exact .thunk (ih e)
  case snval.ne ih _ => exact .ne (ih e)
  case snval.red ihr ihv _ =>
    let ⟨_, e, r⟩ := ihr e
    exact .red r (ihv (Eq.symm e))
  case sncom.lam ih m =>
    cases m <;> try contradiction
    injection e with e
    exact .lam (ih e)
  case sncom.ret ih m =>
    cases m <;> try contradiction
    injection e with e
    exact .ret (ih e)
  case sncom.ne ih _ => exact .ne (ih e)
  case sncom.red ihr ihm _ =>
    let ⟨_, e, r⟩ := ihr e
    exact .red r (ihm (Eq.symm e))
  case srval.thunk ih v =>
    cases v <;> try contradiction
    injection e with e
    let ⟨_, e, r⟩ := ih e; subst e
    exact ⟨.thunk _, rfl, .thunk r⟩
  case srcom.thunk m =>
    cases m <;> try contradiction
    injection e with e
    case force v =>
    cases v <;> try contradiction
    injection e with e
    exact ⟨_, Eq.symm e, .thunk⟩
  case srcom.lam ih m =>
    cases m <;> try contradiction
    injection e with em ev
    case app m _ =>
    cases m <;> try contradiction
    injection em with em
    subst ev em; rw [renameDist]
    exact ⟨_, rfl, .lam (ih rfl)⟩
  case srcom.ret ih m =>
    cases m <;> try contradiction
    injection e with ev em
    case letin m _ =>
    cases m <;> try contradiction
    injection ev with ev
    subst ev em; rw [renameDist]
    exact ⟨_, rfl, .ret (ih rfl)⟩
  case srcom.force ih m =>
    cases m <;> try contradiction
    injection e with e
    let ⟨_, e, r⟩ := ih e; subst e
    exact ⟨.force _, rfl, .force r⟩
  case srcom.app ih m =>
    cases m <;> try contradiction
    injection e with em ev
    let ⟨_, em, r⟩ := ih em; subst em ev
    exact ⟨.app _ _, rfl, .app r⟩
  case srcom.letin ih m =>
    cases m <;> try contradiction
    injection e with em ev
    let ⟨_, em, r⟩ := ih em; subst em ev
    exact ⟨.letin _ _, rfl, .letin r⟩

def SNCom.antirenaming {ξ m} := @(@_root_.antirenaming ξ).right.right.right.left m

theorem extensionality {m x} (h : SNCom (app m (var x))) : SNCom m := by
  generalize e : app m (var x) = m' at h
  mutual_induction h generalizing m x
  case motive_1 => exact λ _ _ ↦ True
  case motive_2 => exact λ _ _ ↦ True
  case motive_3 => exact λ _ _ ↦ True
  case motive_5 => exact λ _ _ _ ↦ True
  case motive_6 => exact λ _ _ _ ↦ True
  all_goals first | simp | contradiction | subst e
  case ne h => cases h with | _ snem => exact .ne snem
  case red r =>
    cases r
    case lam snm _ =>
      rw [substToRename] at snm
      exact .lam (SNCom.antirenaming snm)
    case app r _ h => exact .red r (h rfl)
