import CBPV.Reduction

open Val Com

/-*---------------------------------
  Traditional strong normalization
  as accessibility on reduction
---------------------------------*-/

inductive StepVal.SN : Val → Prop where
  | sn {v} : (∀ {w}, v ⤳ᵛ w → StepVal.SN w) → StepVal.SN v

inductive StepCom.SN : Com → Prop where
  | sn {m} : (∀ {n}, m ⤳ᶜ n → StepCom.SN n) → StepCom.SN m

theorem StepVals.SN {v w} (r : v ⤳⋆ᵛ w) (h : StepVal.SN v) : StepVal.SN w := by
  induction r
  case refl => assumption
  case trans r _ ih => cases h with | _ ihSN => exact ih (ihSN r)

theorem StepComs.SN {m n} (r : m ⤳⋆ᶜ n) (h : StepCom.SN m) : StepCom.SN n := by
  induction r
  case refl => assumption
  case trans r _ ih => cases h with | _ ihSN => exact ih (ihSN r)

/-*-----------------------
  Inversion lemmas on SN
-----------------------*-/

theorem StepCom.SN.force_inv {v} (h : StepCom.SN (.force v)) : StepVal.SN v := by
  generalize e : Com.force v = m at h
  induction h generalizing v; subst e
  case sn ih =>
  constructor; intro _ r
  exact ih (.force r) rfl

theorem StepCom.SN.app_inv {m v} (h : StepCom.SN (.app m v)) : StepCom.SN m := by
  generalize e : Com.app m v = n at h
  induction h generalizing m; subst e
  case sn ih =>
  constructor; intro _ r
  exact ih (.app₁ r) rfl

theorem StepCom.SN.letin_inv {m₁ m₂} (h : StepCom.SN (.letin m₁ m₂)) : StepCom.SN m₁ := by
  generalize e : Com.letin m₁ m₂ = n at h
  induction h generalizing m₁; subst e
  case sn ih =>
  constructor; intro _ r
  exact ih (.letin₁ r) rfl

/-*---------------
  Head expansion
---------------*-/

theorem StepCom.SN.antisubstitution {m} {v : Val} (snm : StepCom.SN (m⦃v⦄)) (snv : StepVal.SN v) : StepCom.SN m := by
  generalize e : (m⦃v⦄) = n at snm
  induction snm generalizing m v; subst e
  case sn h ih =>
  constructor; intro _ r
  apply ih (.subst _ r) snv rfl

theorem StepCom.SN.force_thunk {m} (snm : StepCom.SN m) : StepCom.SN (.force (.thunk m)) := by
  induction snm
  constructor; intro _ r; cases r
  case a.π h _ => exact .sn h
  case a.force ih _ r =>
    cases r with | thunk r => exact ih r

theorem StepCom.SN.app_lam' {m v} (snm : StepCom.SN m) (snv : StepVal.SN v) (snmv : StepCom.SN (m⦃v⦄)): StepCom.SN (Com.app (Com.lam m) v) := by
  induction snv generalizing m
  induction snm
  case sn.sn ihv _ hm ihm =>
  constructor; intro _ r; cases r
  case a.β h _ => exact snmv
  case a.app₁ r =>
    cases r with | lam r =>
    cases snmv with | sn h =>
    exact ihm r (h (.subst _ r))
  case a.app₂ m _ r =>
    let snnv := (StepComs.replace r).SN snmv
    exact ihv r (.sn hm) snnv

theorem StepCom.SN.app_lam {m v} (snv : StepVal.SN v) (snmv : StepCom.SN (m⦃v⦄)): StepCom.SN (Com.app (Com.lam m) v) :=
  .app_lam' (.antisubstitution snmv snv) snv snmv

theorem StepCom.SN.letin_ret' {m v} (snm : StepCom.SN m) (snv : StepVal.SN v) (snmv : StepCom.SN (m⦃v⦄)) : StepCom.SN (Com.letin (Com.ret v) m) := by
  induction snv generalizing m
  induction snm
  case sn.sn ihv _ hm ihm =>
  constructor; intro _ r; cases r
  case a.ζ h _ => exact snmv
  case a.letin₁ ih _ r =>
    cases r with | ret r =>
    let snnv := (StepComs.replace r).SN snmv
    exact ihv r (.sn hm) snnv
  case a.letin₂ r =>
    cases snmv with | sn h =>
    exact ihm r (h (.subst _ r))

theorem StepCom.SN.letin_ret {m v} (snv : StepVal.SN v) (snmv : StepCom.SN (m⦃v⦄)) : StepCom.SN (Com.letin (Com.ret v) m) :=
  .letin_ret' (.antisubstitution snmv snv) snv snmv

theorem StepCom.SN.case_inl' {v m n} (snv : StepVal.SN v) (snm : StepCom.SN m) (snn : StepCom.SN n) (snmv : StepCom.SN (m⦃v⦄)) : StepCom.SN (.case (.inl v) m n) := by
  induction snv generalizing m n
  induction snm generalizing n
  induction snn
  case sn.sn ihv _ hm ihm _ hn ihn =>
  constructor; intro _ r; cases r
  case a.ιl h _ => exact snmv
  case a.case ih _ r =>
    cases r with | inl r =>
    let snnv := (StepComs.replace r).SN snmv
    exact ihv r (.sn hm) (.sn hn) snnv
  case a.case₁ r =>
    cases snmv with | sn h =>
    exact ihm r (.sn hn) (h (.subst _ r))
  case a.case₂ r => exact ihn r

theorem StepCom.SN.case_inl {v m n} (snv : StepVal.SN v) (snmv : StepCom.SN (m⦃v⦄)) (snn : StepCom.SN n) : StepCom.SN (.case (.inl v) m n) :=
  .case_inl' snv (.antisubstitution snmv snv) snn snmv

theorem StepCom.SN.case_inr' {v m n} (snv : StepVal.SN v) (snm : StepCom.SN m) (snn : StepCom.SN n) (snnv : StepCom.SN (n⦃v⦄)) : StepCom.SN (.case (.inr v) m n) := by
  induction snv generalizing m n
  induction snm generalizing n
  induction snn
  case sn.sn ihv _ hm ihm _ hn ihn =>
  constructor; intro _ r; cases r
  case a.ιr h _ => exact snnv
  case a.case ih _ r =>
    cases r with | inr r =>
    let snnv := (StepComs.replace r).SN snnv
    exact ihv r (.sn hm) (.sn hn) snnv
  case a.case₁ r => exact ihm r (.sn hn) snnv
  case a.case₂ r =>
    cases snnv with | sn h =>
    exact ihn r (h (.subst _ r))

theorem StepCom.SN.case_inr {v m n} (snv : StepVal.SN v) (snm : StepCom.SN m) (snnv : StepCom.SN (n⦃v⦄)) : StepCom.SN (.case (.inr v) m n) :=
  .case_inr' snv snm (.antisubstitution snnv snv) snnv

/-*-----------------
  Strong reduction
-----------------*-/

section
set_option hygiene false
local infix:40 "⤳ⁿ" => StepSN
inductive StepSN : Com → Com → Prop where
  | thunk {m} : force (thunk m) ⤳ⁿ m
  | lam {m : Com} {v} : StepVal.SN v → app (lam m) v ⤳ⁿ m⦃v⦄
  | ret {v m} : StepVal.SN v → letin (ret v) m ⤳ⁿ m⦃v⦄
  | inl {v m n} : StepVal.SN v → StepCom.SN n → case (inl v) m n ⤳ⁿ m⦃v⦄
  | inr {v m n} : StepVal.SN v → StepCom.SN m → case (inr v) m n ⤳ⁿ n⦃v⦄
  | app {m n : Com} {v} : StepVal.SN v → m ⤳ⁿ n → app m v ⤳ⁿ app n v
  | letin {m m' n : Com} : StepCom.SN n → m ⤳ⁿ m' → letin m n ⤳ⁿ letin m' n
end
infix:40 "⤳ⁿ" => StepSN

/-*-----------------------------------------------
  Confluence of single-step and strong reduction
-----------------------------------------------*-/

theorem confluence {m n₁ n₂} (r₁ : m ⤳ᶜ n₁) (r₂ : m ⤳ⁿ n₂) : (∃ m', n₁ ⤳ⁿ m' ∧ n₂ ⤳⋆ᶜ m') ∨ n₁ = n₂ := by
  induction r₂ generalizing n₁ <;> cases r₁
  case thunk.π => exact .inr rfl
  case thunk.force r =>
    cases r with | thunk r => exact .inl ⟨_, .thunk, .once r⟩
  case lam.β => exact .inr rfl
  case lam.app₁ snv _ r =>
    cases r with | lam r =>
    exact .inl ⟨_, .lam snv, .subst _ (.once r)⟩
  case lam.app₂ snv _ r =>
    cases snv with | sn h =>
    exact .inl ⟨_, .lam (h r), .replace r⟩
  case ret.ζ => exact .inr rfl
  case ret.letin₁ snv _ r =>
    cases r with | ret r =>
    cases snv with | sn h =>
    exact .inl ⟨_, .ret (h r), .replace r⟩
  case ret.letin₂ snv _ r =>
    exact .inl ⟨_, .ret snv, .subst _ (.once r)⟩
  case inl.ιl => exact .inr rfl
  case inl.case snv snn _ r =>
    cases r with | inl r =>
    cases snv with | sn h =>
    exact .inl ⟨_, .inl (h r) snn, .replace r⟩
  case inl.case₁ snv snn _ r =>
    exact .inl ⟨_, .inl snv snn, .subst _ (.once r)⟩
  case inl.case₂ snv snn _ r =>
    cases snn with | sn h =>
    exact .inl ⟨_, .inl snv (h r), .refl⟩
  case inr.ιr => exact .inr rfl
  case inr.case snv snm _ r =>
    cases r with | inr r =>
    cases snv with | sn h =>
    exact .inl ⟨_, .inr (h r) snm, .replace r⟩
  case inr.case₁ snv snm _ r =>
    cases snm with | sn h =>
    exact .inl ⟨_, .inr snv (h r), .refl⟩
  case inr.case₂ snv snm _ r =>
    exact .inl ⟨_, .inr snv snm, .subst _ (.once r)⟩
  case app.β r ih => cases r
  case app.app₁ snv _ ih _ r =>
    cases ih r
    case inl h =>
      let ⟨_, r₁', r₂'⟩ := h
      exact .inl ⟨_, .app snv r₁', .app₁ r₂'⟩
    case inr e => subst e; exact .inr rfl
  case app.app₂ snv r₁' _ _ r₂' =>
    cases snv with | sn h =>
    exact .inl ⟨_, .app (h r₂') r₁', .app₂ (.once r₂')⟩
  case letin.ζ r _ => cases r
  case letin.letin₁ snn _ ih _ r =>
    cases ih r
    case inl h =>
      let ⟨_, r₁', r₂'⟩ := h
      exact .inl ⟨_, .letin snn r₁', .letin₁ r₂'⟩
    case inr e => subst e; exact .inr rfl
  case letin.letin₂ snn r₁ ih _ r₂ =>
    cases snn with | sn h =>
    exact .inl ⟨_, .letin (h r₂) r₁, .letin₂ (.once r₂)⟩

/-*-------------------------------------
  Backward closure of strong reduction
-------------------------------------*-/

theorem closure_app {v m n} (r₁ : m ⤳ⁿ n) (snm : StepCom.SN m) (snv : StepVal.SN v) (snapp : StepCom.SN (.app n v)) : StepCom.SN (.app m v) := by
  induction snv generalizing m n
  induction snm generalizing n
  case sn v _ ihv _ hv ihm =>
  constructor; intro _ r; cases r
  case a.β => cases r₁
  case a.app₁ r₂ =>
    cases confluence r₂ r₁
    case inl h =>
      let ⟨_, r₂', r₁'⟩ := h
      let r₁'' := StepComs.app₁ (v := v) r₁'
      exact ihm r₂ r₂' (r₁''.SN snapp)
    case inr e => subst e; exact snapp
  case a.app₂ r =>
    cases snapp with | sn happ =>
    exact ihv r r₁ (.sn hv) (happ (.app₂ r))

theorem closure_letin {m m' n} (r₁ : m ⤳ⁿ m') (snm : StepCom.SN m) (snn : StepCom.SN n) (snlet : StepCom.SN (.letin m' n)) : StepCom.SN (.letin m n) := by
  induction snn generalizing m m'
  induction snm generalizing m'
  case sn n _ ihn _ hn ihm =>
  constructor; intro _ r; cases r
  case a.ζ => cases r₁
  case a.letin₁ r₂ =>
    cases confluence r₂ r₁
    case inl h =>
      let ⟨_, r₂', r₁'⟩ := h
      let r₁'' := StepComs.letin₁ (n := n) r₁'
      exact ihm r₂ r₂' (r₁''.SN snlet)
    case inr e => subst e; exact snlet
  case a.letin₂ r =>
    cases snlet with | sn hlet =>
    exact ihn r r₁ (.sn hn) (hlet (.letin₂ r))

theorem StepSN.closure {m n} (r : m ⤳ⁿ n) (snn : StepCom.SN n) : StepCom.SN m := by
  induction r
  case thunk => exact .force_thunk snn
  case lam snv => exact .app_lam snv snn
  case ret snv => exact .letin_ret snv snn
  case inl snv snm => exact .case_inl snv snn snm
  case inr snv snm => exact .case_inr snv snm snn
  case app snv rn ih => exact closure_app rn (ih snn.app_inv) snv snn
  case letin snm rn ih => exact closure_letin rn (ih snn.letin_inv) snm snn

/-*--------------
  Neutral terms
--------------*-/

@[simp, reducible] def NeVal (v : Val) : Prop := ∃ x, v = var x
@[simp, reducible] def NeCom (m : Com) : Prop :=
  match m with
  | force v => NeVal v
  | app m _ => NeCom m
  | letin m _ => NeCom m
  | case v _ _ => NeVal v
  | _ => False

theorem preservation :
  (∀ {v w}, v ⤳ᵛ w → NeVal v → NeVal w) ∧
  (∀ {m n}, m ⤳ᶜ n → NeCom m → NeCom n) := by
  refine ⟨λ r ↦ ?neval, λ r ↦ ?necom⟩
  mutual_induction r, r
  all_goals intro ne; try simp at *
  case necom.force ih | necom.case ih => let ⟨x, e⟩ := ne; exact ih x e
  all_goals apply_rules

def StepVal.preservation {v w} := @_root_.preservation.left  v w
def StepCom.preservation {m n} := @_root_.preservation.right m n

/-*---------------------------
  Congruence rules on SN/SNe
---------------------------*-/

theorem StepVal.SN.inl {v} (h : StepVal.SN v) : StepVal.SN (.inl v) := by
  induction h; constructor; intro _ r; cases r
  case _ ih _ r => exact ih r

theorem StepVal.SN.inr {v} (h : StepVal.SN v) : StepVal.SN (.inr v) := by
  induction h; constructor; intro _ r; cases r
  case _ ih _ r => exact ih r

theorem StepVal.SN.thunk {m} (h : StepCom.SN m) : StepVal.SN (.thunk m) := by
  induction h; constructor; intro _ r; cases r
  case _ ih _ r => exact ih r

theorem StepCom.SN.lam {m} (h : StepCom.SN m) : StepCom.SN (.lam m) := by
  induction h; constructor; intro _ r; cases r
  case _ ih _ r => exact ih r

theorem StepCom.SN.ret {v} (h : StepVal.SN v) : StepCom.SN (.ret v) := by
  induction h; constructor; intro _ r; cases r
  case _ ih _ r => exact ih r

theorem StepCom.SN.force {v} (h : NeVal v) : StepCom.SN (.force v) := by
  induction h; constructor; intro _ r; cases r
  case π => contradiction
  case force e _ r => subst e; cases r

theorem StepCom.SN.app {m v} (nem : NeCom m) (snm : StepCom.SN m) (snv : StepVal.SN v) : StepCom.SN (app m v) := by
  induction snm generalizing v
  induction snv
  case sn.sn ihv _ hv ihm =>
  constructor; intro _ r
  cases r
  case a.β => cases nem
  case a.app₁ r => exact ihv r (r.preservation nem) (.sn hv)
  case a.app₂ r => exact ihm r

theorem StepCom.SN.letin {m n} (nem : NeCom m) (snm : StepCom.SN m) (snn : StepCom.SN n) : StepCom.SN (letin m n) := by
  induction snm generalizing n
  induction snn
  case sn.sn ihm _ hm ihn =>
  constructor; intro _ r
  cases r
  case a.ζ => cases nem
  case a.letin₁ r => exact ihm r (r.preservation nem) (.sn hm)
  case a.letin₂ r => exact ihn r

theorem StepCom.SN.case {v m n} (nev : NeVal v) (snm : StepCom.SN m) (snn : StepCom.SN n) : StepCom.SN (.case v m n) := by
  induction snm generalizing n
  induction snn
  case sn.sn ihm _ hm ihn =>
  constructor; intro _ r
  cases r
  case a.ιl => cases nev; contradiction
  case a.ιr => cases nev; contradiction
  case a.case r => cases r <;> cases nev <;> contradiction
  case a.case₁ r => exact ihm r (.sn hm)
  case a.case₂ r => exact ihn r
