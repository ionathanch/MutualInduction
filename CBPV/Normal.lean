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

inductive SNVal : Val → Prop where
  | var {x} : SNVal (var x)
  | unit : SNVal unit
  | inl {v} : SNVal v → SNVal (inl v)
  | inr {v} : SNVal v → SNVal (inr v)
  | thunk {m} : SNCom m → SNVal (thunk m)

inductive SNCom : Com → Prop where
  | lam {m} : SNCom m → SNCom (lam m)
  | ret {v} : SNVal v → SNCom (ret v)
  | ne {m} : SNeCom m → SNCom m
  | red {m n : Com} : m ⤳ n → SNCom n → SNCom m

inductive SR : Com → Com → Prop where
  | thunk {m} : force (thunk m) ⤳ m
  | lam {m : Com} {v} : SNVal v → app (lam m) v ⤳ m⦃v⦄
  | ret {v m} : SNVal v → letin (ret v) m ⤳ m⦃v⦄
  | inl {v m n} : SNVal v → SNCom m → SNCom n → case (inl v) m n ⤳ m⦃v⦄
  | inr {v m n} : SNVal v → SNCom m → SNCom n → case (inr v) m n ⤳ n⦃v⦄
  | app {m n : Com} {v} : SNVal v → m ⤳ n → app m v ⤳ app n v
  | letin {m m' n : Com} : SNCom n → m ⤳ m' → letin m n ⤳ letin m' n
end
end
infix:40 "⤳" => SR

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

theorem SNCom.case_inv {v m₁ m₂} (h : SNCom (case v m₁ m₂)) : SNVal v ∧ SNCom m₁ ∧ SNCom m₂ := by
  generalize e : case v m₁ m₂ = n at h
  mutual_induction h generalizing v m₁ m₂
  all_goals first | contradiction | subst e
  case ne sne =>
    match sne with
    | .case ⟨_, e⟩ snm₁ snm₂ => subst e; exact ⟨.var, snm₁, snm₂⟩
  case red sn ih r =>
    cases r
    case inl snv snm₁ snm₂ => exact ⟨.inl snv, snm₁, snm₂⟩
    case inr snv snm₁ snm₂ => exact ⟨.inr snv, snm₁, snm₂⟩

theorem SNCom.lam_inv {m} (h : SNCom (.lam m)) : SNCom m := by
  generalize e : Com.lam m = n at h
  mutual_induction h generalizing m
  all_goals first | contradiction | injection e | subst e
  case lam e => subst e; assumption
  case ne sne => cases sne
  case red r => cases r

theorem SNCom.ret_inv {v} (h : SNCom (.ret v)) : SNVal v := by
  generalize e : Com.ret v = m at h
  mutual_induction h generalizing v
  all_goals first | contradiction | injection e | subst e
  case ret e => subst e; assumption
  case ne sne => cases sne
  case red r => cases r

/-*---------------------------------------
  Transitive closure of strong reduction
---------------------------------------*-/

section
set_option hygiene false
local infix:40 "⤳⋆" => SRs
inductive SRs : Com → Com → Prop where
  | refl {m : Com} : m ⤳⋆ m
  | trans {k m n : Com} : k ⤳ m → m ⤳⋆ n → k ⤳⋆ n
end
infix:40 "⤳⋆" => SRs

@[refl] def SRs.rfl {m} := @SRs.refl m

def SRs.once {m n : Com} (r : m ⤳ n) : m ⤳⋆ n := .trans r .refl

theorem SRs.trans' {k m n : Com} (r₁ : k ⤳⋆ m) (r₂ : m ⤳⋆ n) : k ⤳⋆ n := by
  induction r₁ generalizing n
  case refl => exact r₂
  case trans r _ ih => exact .trans r (ih r₂)

instance : Trans SRs SRs SRs where
  trans := SRs.trans'

/-*-------------------------------
  Congruence on strong reduction
-------------------------------*-/

theorem SRs.app {m n : Com} {v} (r : m ⤳⋆ n) (snv : SNVal v): app m v ⤳⋆ app n v := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.app snv r₁) r₂

theorem SRs.letin {m m' n : Com} (r : m ⤳⋆ m') (snn : SNCom n) : letin m n ⤳⋆ letin m' n := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.letin snn r₁) r₂

/-*----------------------------------------
  Backward closure wrt strong reduction
  N.B. SNeComs are *not* backward closed,
  e.g. force (thunk (force x)) ⤳ force x
----------------------------------------*-/

theorem SRs.closure {m n : Com} (r : m ⤳⋆ n) (h : SNCom n) : SNCom m := by
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
  case sncom.ne ih _ => exact .ne (ih e)
  case sncom.red ihr ihm _ =>
    let ⟨_, e, r⟩ := ihr e
    exact .red r (ihm (Eq.symm e))
  case srcom.thunk ih m =>
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
  case srcom.inl ihv ihm ihn m =>
    cases m <;> try contradiction
    injection e with ev em en
    rename Val => v
    cases v <;> try contradiction
    injection ev with ev
    subst ev em en; rw [renameDist]
    exact ⟨_, rfl, .inl (ihv rfl) (ihm rfl) (ihn rfl)⟩
  case srcom.inr ihv ihm ihn m =>
    cases m <;> try contradiction
    injection e with ev em en
    rename Val => v
    cases v <;> try contradiction
    injection ev with ev
    subst ev em en; rw [renameDist]
    exact ⟨_, rfl, .inr (ihv rfl) (ihm rfl) (ihn rfl)⟩
  case srcom.app ihv ihm m =>
    cases m <;> try contradiction
    injection e with em ev
    let ⟨_, em, r⟩ := ihm em; subst em ev
    exact ⟨.app _ _, rfl, .app (ihv rfl) r⟩
  case srcom.letin ihn ihm  m =>
    cases m <;> try contradiction
    injection e with em ev
    let ⟨_, em, r⟩ := ihm em; subst em ev
    exact ⟨.letin _ _, rfl, .letin (ihn rfl) r⟩

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
    case app r _ _ h => exact .red r (h rfl)
