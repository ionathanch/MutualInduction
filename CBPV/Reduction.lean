import CBPV.Normal

open Val Com

/-*----------------------
  Single-step reduction
----------------------*-/

section
set_option hygiene false
local infix:40 "⤳ᵛ" => StepVal
local infix:40 "⤳ᶜ" => StepCom

mutual
inductive StepVal : Val → Val → Prop where
  | inl {v w} : v ⤳ᵛ w → inl v ⤳ᵛ inl w
  | inr {v w} : v ⤳ᵛ w → inr v ⤳ᵛ inr w
  | thunk {m n} : m ⤳ᶜ n → thunk m ⤳ᵛ thunk n

inductive StepCom : Com → Com → Prop where
  | π {m} : force (thunk m) ⤳ᶜ m
  | β {m v} : app (lam m) v ⤳ᶜ m⦃v⦄
  | ζ {v m} : letin (ret v) m ⤳ᶜ m⦃v⦄
  | ιl {v m n} : case (inl v) m n ⤳ᶜ m⦃v⦄
  | ιr {v m n} : case (inr v) m n ⤳ᶜ n⦃v⦄
  | force {v w} : v ⤳ᵛ w → force v ⤳ᶜ force w
  | lam {m n} : m ⤳ᶜ n → lam m ⤳ᶜ lam n
  | app₁ {m n v} :
    m ⤳ᶜ n →
    -------------------
    app m v ⤳ᶜ app n v
  | app₂ {m v w} :
    v ⤳ᵛ w →
    -------------------
    app m v ⤳ᶜ app m w
  | ret {v w} : v ⤳ᵛ w → ret v ⤳ᶜ ret w
  | letin₁ {m m' n} :
    m ⤳ᶜ m' →
    ------------------------
    letin m n ⤳ᶜ letin m' n
  | letin₂ {m n n'} :
    n ⤳ᶜ n' →
    ------------------------
    letin m n ⤳ᶜ letin m n'
  | case {v w m n} :
    v ⤳ᵛ w →
    -------------------------
    case v m n ⤳ᶜ case w m n
  | case₁ {v m m' n} :
    m ⤳ᶜ m' →
    --------------------------
    case v m n ⤳ᶜ case v m' n
  | case₂ {v m n n'} :
    n ⤳ᶜ n' →
    --------------------------
    case v m n ⤳ᶜ case v m n'
end
end

infix:40 "⤳ᵛ" => StepVal
infix:40 "⤳ᶜ" => StepCom

/-*---------------------
  Multi-step reduction
---------------------*-/

section
set_option hygiene false
local infix:40 "⤳⋆ᵛ" => StepVals
local infix:40 "⤳⋆ᶜ" => StepComs

inductive StepVals : Val → Val → Prop where
  | refl {a} : a ⤳⋆ᵛ a
  | trans {a b c} : a ⤳ᵛ b → b ⤳⋆ᵛ c → a ⤳⋆ᵛ c

inductive StepComs : Com → Com → Prop where
  | refl {a} : a ⤳⋆ᶜ a
  | trans {a b c} : a ⤳ᶜ b → b ⤳⋆ᶜ c → a ⤳⋆ᶜ c
end

infix:40 "⤳⋆ᵛ" => StepVals
infix:40 "⤳⋆ᶜ" => StepComs

def StepVals.once {a b} (r : a ⤳ᵛ b) : a ⤳⋆ᵛ b := .trans r .refl
def StepComs.once {a b} (r : a ⤳ᶜ b) : a ⤳⋆ᶜ b := .trans r .refl

theorem StepVals.trans' {a b c} (r₁ : a ⤳⋆ᵛ b) (r₂ : b ⤳⋆ᵛ c) : a ⤳⋆ᵛ c := by
  induction r₁ generalizing c
  case refl => exact r₂
  case trans r₁ _ ih => exact .trans r₁ (ih r₂)

theorem StepComs.trans' {a b c} (r₁ : a ⤳⋆ᶜ b) (r₂ : b ⤳⋆ᶜ c) : a ⤳⋆ᶜ c := by
  induction r₁ generalizing c
  case refl => exact r₂
  case trans r₁ _ ih => exact .trans r₁ (ih r₂)

/-*-----------------------------------------
  Congruence rules on multi-step reduction
-----------------------------------------*-/

theorem StepComs.app₁ {m n v} (r : m ⤳⋆ᶜ n) : app m v ⤳⋆ᶜ app n v := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.app₁ r₁) r₂

theorem StepComs.app₂ {m v w} (r : v ⤳⋆ᵛ w) : app m v ⤳⋆ᶜ app m w := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.app₂ r₁) r₂

/-*---------------------------------
  Traditional strong normalization
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

theorem StepVal.SN.inl_inv {v} (h : StepVal.SN (.inl v)) : StepVal.SN v := by
  generalize e : Val.inl v = w at h
  induction h generalizing v; subst e
  case sn ih =>
  constructor; intro _ r
  exact ih (.inl r) rfl

theorem StepVal.SN.thunk_inv {m} (h : StepVal.SN (.thunk m)) : StepCom.SN m := by
  generalize e : Val.thunk m = v at h
  induction h generalizing m; subst e
  case sn ih =>
  constructor; intro _ r
  exact ih (.thunk r) rfl

theorem StepCom.SN.lam_inv {m} (h : StepCom.SN (.lam m)) : StepCom.SN m := by
  generalize e : Com.lam m = n at h
  induction h generalizing m; subst e
  case sn ih =>
  constructor; intro _ r
  exact ih (.lam r) rfl

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

/-*-----------------------
  Congruence rules on SN
-----------------------*-/

theorem StepVal.SN.inl {v} (h : StepVal.SN v) : StepVal.SN (.inl v) := by
  induction h; constructor; intro _ r; cases r
  case _ ih _ r => exact ih r

theorem StepVal.SN.inr {v} (h : StepVal.SN v) : StepVal.SN (.inr v) := by
  induction h; constructor; intro _ r; cases r
  case _ ih _ r => exact ih r

theorem StepVal.SN.thunk {m} (h : StepCom.SN m) : StepVal.SN (.thunk m) := by
  induction h; constructor; intro _ r; cases r
  case _ ih _ r => exact ih r

theorem StepCom.SN.force {v} (h : StepVal.SN v) : StepCom.SN (.force v) := by
  induction h; constructor; intro _ r; cases r
  case π h _ => exact (StepVal.SN.sn h).thunk_inv
  case force ih _ r => exact ih r

theorem StepCom.SN.lam {m} (h : StepCom.SN m) : StepCom.SN (.lam m) := by
  induction h; constructor; intro _ r; cases r
  case _ ih _ r => exact ih r

theorem StepCom.SN.ret {v} (h : StepVal.SN v) : StepCom.SN (.ret v) := by
  induction h; constructor; intro _ r; cases r
  case _ ih _ r => exact ih r

/-*--------------
  SN on redexes
--------------*-/

theorem StepCom.SN.force_thunk {m} (snm : StepCom.SN m) : StepCom.SN (.force (.thunk m)) := by
  induction snm
  constructor; intro _ r; cases r
  case a.π h _ => exact .sn h
  case a.force ih _ r =>
    cases r with | thunk r => exact ih r

theorem StepCom.SN.app_lam {m v} (snv : StepVal.SN v) (snm : StepCom.SN (m⦃v⦄)) : StepCom.SN (Com.app (Com.lam m) v) := by
  generalize e : (m⦃v⦄) = n at snm
  induction snm generalizing m v; subst e
  constructor; intro _ r; cases r
  case a.β h _ => exact .sn h
  case a.app₁ ih _ r =>
    cases r with | lam r =>
    refine ih ?_ snv rfl; sorry -- substitution
  case a.app₂ ih _ r =>
    cases snv with | sn h =>
    refine ih ?_ (h r) rfl; sorry -- substitution

theorem StepCom.SN.letin_ret {m v} (snv : StepVal.SN v) (snm : StepCom.SN (m⦃v⦄)) : StepCom.SN (Com.letin (Com.ret v) m) := by
  generalize e : (m⦃v⦄) = n at snm
  induction snm generalizing m v; subst e
  constructor; intro _ r; cases r
  case a.ζ h _ => exact .sn h
  case a.letin₁ ih _ r =>
    cases r with | ret r =>
    cases snv with | sn h =>
    refine ih ?_ (h r) rfl; sorry -- substitution
  case a.letin₂ ih _ r =>
    refine ih ?_ snv rfl; sorry -- substitution

theorem StepCom.SN.case_inl {v m n} (snv : StepVal.SN v) (snm : StepCom.SN (m⦃v⦄)) (snn : StepCom.SN n) : StepCom.SN (.case (.inl v) m n) := by
  generalize e : (m⦃v⦄) = m' at snm
  induction snm generalizing v m n; subst e
  constructor; intro _ r; cases r
  case a.ιl h _ => exact .sn h
  case a.case ih _ r =>
    cases r with | inl r =>
    cases snv with | sn h =>
    refine ih ?_ (h r) snn rfl; sorry -- substitution
  case a.case₁ ih _ r =>
    refine ih ?_ snv snn rfl; sorry -- substitution
  case a.case₂ ih _ r =>
    cases snn with | sn h =>
    refine ih ?_ snv (h r) rfl; sorry -- substitution

theorem StepCom.SN.case_inr {v m n} (snv : StepVal.SN v) (snm : StepCom.SN m) (snn : StepCom.SN (n⦃v⦄)) : StepCom.SN (.case (.inr v) m n) := by
  generalize e : (n⦃v⦄) = n' at snn
  induction snn generalizing v m n; subst e
  constructor; intro _ r; cases r
  case a.ιr h _ => exact .sn h
  case a.case ih _ r =>
    cases r with | inr r =>
    cases snv with | sn h =>
    refine ih ?_ (h r) snm rfl; sorry -- substitution
  case a.case₁ ih _ r =>
    cases snm with | sn h =>
    refine ih ?_ snv (h r) rfl; sorry -- substitution
  case a.case₂ ih _ r =>
    refine ih ?_ snv snm rfl; sorry -- substitution

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
  | inl {v m n} : StepVal.SN v → StepCom.SN m → StepCom.SN n → case (inl v) m n ⤳ⁿ m⦃v⦄
  | inr {v m n} : StepVal.SN v → StepCom.SN m → StepCom.SN n → case (inr v) m n ⤳ⁿ n⦃v⦄
  | app {m n : Com} {v} : StepVal.SN v → m ⤳ⁿ n → app m v ⤳ⁿ app n v
  | letin {m m' n : Com} : StepCom.SN n → m ⤳ⁿ m' → letin m n ⤳ⁿ letin m' n
end
infix:40 "⤳ⁿ" => StepSN

/-*-----------------------------------------------
  Confluence of single-step and strong reduction
-----------------------------------------------*-/

theorem confluence {m n₁ n₂} (r₁ : m ⤳ᶜ n₁) (r₂ : m ⤳ⁿ n₂) : (∃ m', n₁ ⤳ⁿ m' ∧ n₂ ⤳ᶜ m') ∨ n₁ = n₂ := by
  induction r₂ generalizing n₁ <;> cases r₁
  case lam.β => exact .inr rfl
  case lam.app₁ snv _ r =>
    cases r; case lam r =>
    refine .inl ⟨_, .lam snv, ?_⟩; sorry -- substitution
  case lam.app₂ snv _ r =>
    cases snv; case sn h =>
    refine .inl ⟨_, .lam (h r), ?_⟩; sorry -- substitution
  case app.β r ih => cases r
  case app.app₁ snv _ ih _ r =>
    cases ih r
    case inl h =>
      let ⟨_, r₁', r₂'⟩ := h
      exact .inl ⟨_, .app snv r₁', .app₁ r₂'⟩
    case inr e => subst e; exact .inr rfl
  case app.app₂ snv r₁' _ _ r₂' =>
    cases snv; case sn h =>
    exact .inl ⟨_, .app (h r₂') r₁', .app₂ r₂'⟩
  all_goals sorry

/-*-------------------------------------
  Backward closure of strong reduction
-------------------------------------*-/

theorem closure_app {v m n} (r₁ : m ⤳ⁿ n) (snm : StepCom.SN m) (snv : StepVal.SN v) (snapp : StepCom.SN (.app n v)) : StepCom.SN (.app m v) := by
  constructor; intro _ r; cases r
  case a.β => cases r₁
  case a.app₁ r₂ =>
    cases confluence r₂ r₁
    case inl h =>
      let ⟨_, r₂', r₁'⟩ := h
      cases snm with | sn hm =>
      cases snapp with | sn happ =>
      exact closure_app r₂' (hm r₂) snv (happ (.app₁ r₁'))
    case inr e => subst e; exact snapp
  case a.app₂ r =>
    cases snv with | sn hv =>
    cases snapp with | sn happ =>
    exact closure_app r₁ snm (hv r) (happ (.app₂ r))
termination_by sizeOf snm + sizeOf snv
decreasing_by all_goals sorry

theorem closure_letin {m m' n} (r₁ : m ⤳ⁿ m') (snm : StepCom.SN m) (snn : StepCom.SN n) (snlet : StepCom.SN (.letin m' n)) : StepCom.SN (.letin m n) := by
  constructor; intro _ r; cases r
  case a.ζ => cases r₁
  case a.letin₁ r₂ =>
    cases confluence r₂ r₁
    case inl h =>
      let ⟨_, r₂', r₁'⟩ := h
      cases snm with | sn hm =>
      cases snlet with | sn hlet =>
      exact closure_letin r₂' (hm r₂) snn (hlet (.letin₁ r₁'))
    case inr e => subst e; exact snlet
  case a.letin₂ r =>
    cases snn with | sn hn =>
    cases snlet with | sn hlet =>
    exact closure_letin r₁ snm (hn r) (hlet (.letin₂ r))
termination_by sizeOf snm + sizeOf snn
decreasing_by all_goals sorry

theorem StepSN.closure {m n} (r : m ⤳ⁿ n) (snn : StepCom.SN n) : StepCom.SN m := by
  induction r
  case thunk => exact .force_thunk snn
  case lam snv => exact .app_lam snv snn
  case ret snv => exact .letin_ret snv snn
  case inl snv _ snm => exact .case_inl snv snn snm
  case inr snv snm _ => exact .case_inr snv snm snn
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

/-*----------------------------------
  Congruence rules on neutral terms
----------------------------------*-/

theorem StepCom.SN.app {m v} (nem : NeCom m) (snm : StepCom.SN m) (snv : StepVal.SN v) : StepCom.SN (app m v) := by
  constructor; intro _ r
  cases r
  case a.β => cases nem
  case a.app₁ r =>
    cases snm
    case sn h => exact .app (r.preservation nem) (h r) snv
  case a.app₂ r =>
    cases snv
    case sn h => exact .app nem snm (h r)
termination_by sizeOf snm + sizeOf snv
decreasing_by all_goals sorry

theorem StepCom.SN.letin {m n} (nem : NeCom m) (snm : StepCom.SN m) (snn : StepCom.SN n) : StepCom.SN (letin m n) := by
  constructor; intro _ r
  cases r
  case a.ζ => cases nem
  case a.letin₁ r =>
    cases snm
    case sn h => exact .letin (r.preservation nem) (h r) snn
  case a.letin₂ r =>
    cases snn
    case sn h => exact .letin nem snm (h r)
termination_by sizeOf snm + sizeOf snn
decreasing_by all_goals sorry

theorem StepCom.SN.case {v m n} (nev : NeVal v) (snm : StepCom.SN m) (snn : StepCom.SN n) : StepCom.SN (.case v m n) := by
  constructor; intro _ r
  cases r
  case a.ιl => cases nev; contradiction
  case a.ιr => cases nev; contradiction
  case a.case r => cases r <;> cases nev <;> contradiction
  case a.case₁ r =>
    cases snm
    case sn h => exact .case nev (h r) snn
  case a.case₂ r =>
    cases snn
    case sn h => exact .case nev snm (h r)
termination_by sizeOf snm + sizeOf snn
decreasing_by all_goals sorry

/-*--------------------------
  Soundness of SNCom/SNVal
  wrt StepVal.SN/StepCom.SN
--------------------------*-/

theorem NeCom.ne {m} (snem : SNeCom m) : NeCom m := by
  mutual_induction snem <;> assumption

theorem StepVal.SN.ne {v} (h : SNeVal v) : StepVal.SN v := by
  let ⟨_, e⟩ := h; subst e
  constructor; intro _ r; cases r

theorem soundness :
  (∀ {m}, SNeCom m → StepCom.SN m) ∧
  (∀ {v}, SNVal  v → StepVal.SN v) ∧
  (∀ {m}, SNCom  m → StepCom.SN m) ∧
  (∀ {m n : Com}, m ⤳ n → m ⤳ⁿ n) := by
  refine ⟨λ sne ↦ ?snecom, λ sn ↦ ?snval, λ sn ↦ ?sncom, λ r ↦ ?srcom⟩
  mutual_induction sne, sn, sn, r
  case snecom.force ih => exact .force (.ne ih)
  case snecom.app snem _ snm snv => exact .app (.ne snem) snm snv
  case snecom.letin snem _ snm snn => exact .letin (.ne snem) snm snn
  case snecom.case snv _ _ snm snn => exact .case snv snm snn
  case snval.var => constructor; intro _ r; cases r
  case snval.unit => constructor; intro _ r; cases r
  case snval.inl ih => exact .inl ih
  case snval.inr ih => exact .inr ih
  case snval.thunk ih => exact .thunk ih
  case sncom.lam ih => exact .lam ih
  case sncom.ret ih => exact .ret ih
  case sncom.ne => assumption
  case sncom.red r ih => exact r.closure ih
  case srcom.thunk => constructor
  case srcom.lam => constructor; assumption
  case srcom.ret => constructor; assumption
  case srcom.inl => constructor <;> assumption
  case srcom.inr => constructor <;> assumption
  case srcom.app => constructor <;> assumption
  case srcom.letin => constructor <;> assumption
