import CBPV.RTC
import CBPV.Syntax

open ValType ComType Val Com

def SNeVal (v : Val) : Prop := ∃ x, v = var x
def SNeVal.var {x} : SNeVal (var x) := ⟨_, rfl⟩

section
set_option hygiene false
local infix:40 "⤳" => SR
mutual
inductive SNeCom : Com → Prop where
  | force {v} : SNeVal v → SNeCom (force v)
  | app {m v} : SNeCom m → SNVal v → SNeCom (app m v)
  | letin {m n} : SNeCom m → SNCom n → SNeCom (letin m n)
  | case {v m n} : SNeVal v → SNCom m → SNCom n → SNeCom (case v m n)
  | prjl {m} : SNeCom m → SNeCom (prjl m)
  | prjr {m} : SNeCom m → SNeCom (prjr m)

inductive SNVal : Val → Prop where
  | var {x} : SNVal (var x)
  | unit : SNVal unit
  | inl {v} : SNVal v → SNVal (inl v)
  | inr {v} : SNVal v → SNVal (inr v)
  | thunk {m} : SNCom m → SNVal (thunk m)

inductive SNCom : Com → Prop where
  | lam {m} : SNCom m → SNCom (lam m)
  | ret {v} : SNVal v → SNCom (ret v)
  | prod {m n} : SNCom m → SNCom n → SNCom (prod m n)
  | ne {m} : SNeCom m → SNCom m
  | red {m n : Com} : m ⤳ n → SNCom n → SNCom m

inductive SR : Com → Com → Prop where
  | thunk {m} : force (thunk m) ⤳ m
  | lam {m : Com} {v} : SNVal v → app (lam m) v ⤳ m⦃v⦄
  | ret {v m} : SNVal v → letin (ret v) m ⤳ m⦃v⦄
  | inl {v m n} : SNVal v → SNCom n → case (inl v) m n ⤳ m⦃v⦄
  | inr {v m n} : SNVal v → SNCom m → case (inr v) m n ⤳ n⦃v⦄
  | prodl {m n} : SNCom n → prjl (prod m n) ⤳ m
  | prodr {m n} : SNCom m → prjr (prod m n) ⤳ n
  | app {m n : Com} {v} : m ⤳ n → app m v ⤳ app n v
  | letin {m m' n : Com} : m ⤳ m' → letin m n ⤳ letin m' n
  | prjl {m n} : m ⤳ n → prjl m ⤳ prjl n
  | prjr {m n} : m ⤳ n → prjr m ⤳ prjr n
end
end
infix:40 "⤳" => SR

@[reducible] def SRs := RTC SR
infix:40 "⤳⋆" => SRs

/-*-----------------------------------------
  Inversion lemmas on strong normalization
-----------------------------------------*-/

theorem SNCom.force_inv {v} (h : SNCom (force v)) : SNVal v := by
  generalize e : force v = m at h
  mutual_induction h generalizing v
  all_goals first | contradiction | subst e
  case ne sne => match sne with
  | .force ⟨_, e⟩ => subst e; exact .var
  case red sn ih r => cases r; exact .thunk sn

/-*-------------------------------
  Congruence on strong reduction
-------------------------------*-/

theorem SRs.app {m n : Com} {v} (r : m ⤳⋆ n) : app m v ⤳⋆ app n v := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.app r₁) r₂

theorem SRs.letin {m m' n : Com} (r : m ⤳⋆ m') : letin m n ⤳⋆ letin m' n := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.letin r₁) r₂

theorem SRs.prjl {m n : Com} (r : m ⤳⋆ n) : prjl m ⤳⋆ prjl n := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.prjl r₁) r₂

theorem SRs.prjr {m n : Com} (r : m ⤳⋆ n) : prjr m ⤳⋆ prjr n := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.prjr r₁) r₂

theorem SRs.red {m n : Com} (r : m ⤳⋆ n) (h : SNCom n) : SNCom m := by
  induction r
  case refl => assumption
  case trans r _ ih => exact .red r (ih h)

/-*--------------------------------
  Antirenaming and extensionality
--------------------------------*-/

theorem antirenaming {ξ} :
  (∀ {m}, SNeCom (renameCom ξ m) → SNeCom m) ∧
  (∀ {v}, SNVal  (renameVal ξ v) → SNVal v)  ∧
  (∀ {m}, SNCom  (renameCom ξ m) → SNCom m)  ∧
  (∀ {m n}, renameCom ξ m ⤳ n → ∃ n', n = renameCom ξ n' ∧ m ⤳ n') := by
  refine ⟨λ snem ↦ ?snecom, λ snv ↦ ?snval, λ snm ↦ ?sncom, λ r ↦ ?srcom⟩
  case' srcom  => generalize e : renameCom ξ _ = m' at r
  case' sncom  => generalize e : renameCom ξ _ = m' at snm
  case' snval  => generalize e : renameVal ξ _ = v' at snv
  case' snecom => generalize e : renameCom ξ _ = m' at snem
  mutual_induction snem, snv, snm, r generalizing ξ
  case snecom.force ih m =>
    cases m <;> try contradiction
    injection e with e
    case force v =>
    let ⟨_, e⟩ := ih; subst e
    cases v <;> try contradiction
    exact .force .var
  case snecom.app ihm ihv m =>
    cases m <;> try contradiction
    injection e with em ev
    exact .app (ihm em) (ihv ev)
  case snecom.letin ihm ihn m =>
    cases m <;> try contradiction
    injection e with em en
    exact .letin (ihm em) (ihn en)
  case snecom.case snev _ ihv ihm ihn m =>
    cases m <;> try contradiction
    injection e with ev em en
    case case v _ _ =>
    let ⟨_, e⟩ := snev; subst e
    cases v <;> try contradiction
    refine .case .var (ihm em) (ihn en)
  case snecom.prjl ih m =>
    cases m <;> try contradiction
    injection e with e
    exact .prjl (ih e)
  case snecom.prjr ih m =>
    cases m <;> try contradiction
    injection e with e
    exact .prjr (ih e)
  case snval.var ih v =>
    cases v <;> try contradiction
    exact .var
  case snval.unit v => cases v <;> injection e; constructor
  case snval.inl ih v =>
    cases v <;> try contradiction
    injection e with e
    exact .inl (ih e)
  case snval.inr ih v =>
    cases v <;> try contradiction
    injection e with e
    exact .inr (ih e)
  case snval.thunk ih v =>
    cases v <;> try contradiction
    injection e with e
    exact .thunk (ih e)
  case sncom.lam ih m =>
    cases m <;> try contradiction
    injection e with e
    exact .lam (ih e)
  case sncom.ret ih m =>
    cases m <;> try contradiction
    injection e with e
    exact .ret (ih e)
  case sncom.prod ihm ihn m =>
    cases m <;> try contradiction
    injection e with em en
    exact .prod (ihm em) (ihn en)
  case sncom.ne ih _ => exact .ne (ih e)
  case sncom.red ihr ihm _ =>
    let ⟨_, e, r⟩ := ihr e
    exact .red r (ihm (.symm e))
  case srcom.thunk ih m =>
    cases m <;> try contradiction
    injection e with e
    case force v =>
    cases v <;> try contradiction
    injection e with e
    exact ⟨_, .symm e, .thunk⟩
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
  case srcom.inl ihv ihn m =>
    cases m <;> try contradiction
    injection e with ev em en
    rename Val => v
    cases v <;> try contradiction
    injection ev with ev
    subst ev em en; rw [renameDist]
    exact ⟨_, rfl, .inl (ihv rfl) (ihn rfl)⟩
  case srcom.inr ihv ihm m =>
    cases m <;> try contradiction
    injection e with ev em en
    rename Val => v
    cases v <;> try contradiction
    injection ev with ev
    subst ev em en; rw [renameDist]
    exact ⟨_, rfl, .inr (ihv rfl) (ihm rfl)⟩
  case srcom.app ihv ihm m =>
    cases m <;> try contradiction
    injection e with em ev
    let ⟨_, em, r⟩ := ihm em; subst em ev
    exact ⟨.app _ _, rfl, .app r⟩
  case srcom.letin ihm m =>
    cases m <;> try contradiction
    injection e with em ev
    let ⟨_, em, r⟩ := ihm em; subst em ev
    exact ⟨.letin _ _, rfl, .letin r⟩
  case srcom.prodl ihm m =>
    cases m <;> try contradiction
    injection e with e
    rename Com => m
    cases m <;> try contradiction
    injection e with em en
    exact ⟨_, .symm em, .prodl (ihm en)⟩
  case srcom.prodr ihm m =>
    cases m <;> try contradiction
    injection e with e
    rename Com => m
    cases m <;> try contradiction
    injection e with em en
    exact ⟨_, .symm en, .prodr (ihm em)⟩
  case srcom.prjl ihm m =>
    cases m <;> try contradiction
    injection e with e
    let ⟨_, e, r⟩ := ihm e; subst e
    exact ⟨.prjl _, rfl, .prjl r⟩
  case srcom.prjr ihm m =>
    cases m <;> try contradiction
    injection e with e
    let ⟨_, e, r⟩ := ihm e; subst e
    exact ⟨.prjr _, rfl, .prjr r⟩

def SNCom.antirenaming {ξ m} := @(@_root_.antirenaming ξ).right.right.left m

theorem extensionality {m x} (h : SNCom (app m (var x))) : SNCom m := by
  generalize e : app m (var x) = m' at h
  mutual_induction h generalizing m x
  all_goals first | contradiction | subst e
  case ne h => cases h with | app snem => exact .ne snem
  case red r =>
    cases r
    case lam snm _ =>
      rw [substToRename] at snm
      exact .lam (SNCom.antirenaming snm)
    case app r _ h => exact .red r (h rfl)
