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

/-*-------------------------------------------------
  Ω := (λx. (force x) x) (thunk (λx. (force x) x))
  is a diverging term
-------------------------------------------------*-/

def Ω := app ω (thunk ω) where
  ω := lam (app (force (var 0)) (var 0))

theorem loopDiverges {m n} (rmn : m ⤳ᶜ n) (rnm : n ⤳ᶜ m) (snm : StepCom.SN m) : False := by
  induction snm generalizing n
  case sn ih => exact ih rmn rnm rmn

def ΩDiverges : StepCom.SN Ω → False := loopDiverges .β (.app₁ .π)

/-*-----------------------
  Inversion lemmas on SN
-----------------------*-/

theorem StepCom.SN.app_inv₁ {m v} (h : StepCom.SN (.app m v)) : StepCom.SN m := by
  generalize e : Com.app m v = n at h
  induction h generalizing m; subst e
  case sn ih =>
  constructor; intro _ r
  exact ih (.app₁ r) rfl

theorem StepCom.SN.app_inv₂ {m v} (h : StepCom.SN (.app m v)) : StepVal.SN v := by
  generalize e : Com.app m v = n at h
  induction h generalizing v; subst e
  case sn ih =>
  constructor; intro _ r
  exact ih (.app₂ r) rfl

theorem StepCom.SN.letin_inv₁ {m₁ m₂} (h : StepCom.SN (.letin m₁ m₂)) : StepCom.SN m₁ := by
  generalize e : Com.letin m₁ m₂ = n at h
  induction h generalizing m₁; subst e
  case sn ih =>
  constructor; intro _ r
  exact ih (.letin₁ r) rfl

theorem StepCom.SN.letin_inv₂ {m₁ m₂} (h : StepCom.SN (.letin m₁ m₂)) : StepCom.SN m₂ := by
  generalize e : Com.letin m₁ m₂ = n at h
  induction h generalizing m₂; subst e
  case sn ih =>
  constructor; intro _ r
  exact ih (.letin₂ r) rfl

theorem StepCom.SN.fst_inv {m} (h : StepCom.SN (.fst m)) : StepCom.SN m := by
  generalize e : Com.fst m = n at h
  induction h generalizing m; subst e
  case sn ih =>
  constructor; intro _ r
  exact ih (.fst r) rfl

theorem StepCom.SN.snd_inv {m} (h : StepCom.SN (.snd m)) : StepCom.SN m := by
  generalize e : Com.snd m = n at h
  induction h generalizing m; subst e
  case sn ih =>
  constructor; intro _ r
  exact ih (.snd r) rfl

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
  case a.β => exact snmv
  case a.app₁ r =>
    cases r with | lam r =>
    cases snmv with | sn h =>
    exact ihm r (h (.subst _ r))
  case a.app₂ m _ r =>
    let snnv := r.replace.SN snmv
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
    let snnv := r.replace.SN snmv
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
  case a.ιl => exact snmv
  case a.case r =>
    cases r with | inl r =>
    let snnv := r.replace.SN snmv
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
  case a.ιr => exact snnv
  case a.case r =>
    cases r with | inr r =>
    let snnv := r.replace.SN snnv
    exact ihv r (.sn hm) (.sn hn) snnv
  case a.case₁ r => exact ihm r (.sn hn) snnv
  case a.case₂ r =>
    cases snnv with | sn h =>
    exact ihn r (h (.subst _ r))

theorem StepCom.SN.case_inr {v m n} (snv : StepVal.SN v) (snm : StepCom.SN m) (snnv : StepCom.SN (n⦃v⦄)) : StepCom.SN (.case (.inr v) m n) :=
  .case_inr' snv snm (.antisubstitution snnv snv) snnv

theorem StepCom.SN.fst_prod {m n} (snm : StepCom.SN m) (snn : StepCom.SN n) : StepCom.SN (.fst (.prod m n)) := by
  induction snm generalizing n
  induction snn
  constructor; intro _ r; cases r
  case a.π1 h _ _ _ _ => exact .sn h
  case a.fst ihm _ hn ihn _ r =>
    cases r
    case prod₁ r => exact ihm r (.sn hn)
    case prod₂ r => exact ihn r

theorem StepCom.SN.snd_prod {m n} (snm : StepCom.SN m) (snn : StepCom.SN n) : StepCom.SN (.snd (.prod m n)) := by
  induction snn generalizing m
  induction snm
  constructor; intro _ r; cases r
  case a.π2 h _ _ _ _ => exact .sn h
  case a.snd ihn _ hm ihm _ r =>
    cases r
    case prod₁ r => exact ihm r
    case prod₂ r => exact ihn r (.sn hm)

/-*-----------------
  Strong reduction
-----------------*-/

section
set_option hygiene false
local infix:40 "⤳ⁿ" => StepSN
inductive StepSN : Com → Com → Prop where
  | π {m} : force (thunk m) ⤳ⁿ m
  | β {m : Com} {v} : StepVal.SN v → app (lam m) v ⤳ⁿ m⦃v⦄
  | ζ {v m} : StepVal.SN v → letin (ret v) m ⤳ⁿ m⦃v⦄
  | ι1 {v m n} : StepVal.SN v → StepCom.SN n → case (inl v) m n ⤳ⁿ m⦃v⦄
  | ι2 {v m n} : StepVal.SN v → StepCom.SN m → case (inr v) m n ⤳ⁿ n⦃v⦄
  | π1 {m n} : StepCom.SN n → fst (prod m n) ⤳ⁿ m
  | π2 {m n} : StepCom.SN m → snd (prod m n) ⤳ⁿ n
  | app {m n : Com} {v} : m ⤳ⁿ n → app m v ⤳ⁿ app n v
  | letin {m m' n : Com} : m ⤳ⁿ m' → letin m n ⤳ⁿ letin m' n
  | fst {m n} : m ⤳ⁿ n → fst m ⤳ⁿ fst n
  | snd {m n} : m ⤳ⁿ n → snd m ⤳ⁿ snd n
end
infix:40 "⤳ⁿ" => StepSN

/-*-----------------------------------------------
  Confluence of single-step and strong reduction
-----------------------------------------------*-/

theorem confluence {m n₁ n₂} (r₁ : m ⤳ᶜ n₁) (r₂ : m ⤳ⁿ n₂) : (∃ m', n₁ ⤳ⁿ m' ∧ n₂ ⤳⋆ᶜ m') ∨ n₁ = n₂ := by
  induction r₂ generalizing n₁ <;> cases r₁
  case π.π => exact .inr rfl
  case π.force r =>
    cases r with | thunk r => exact .inl ⟨_, .π, .once r⟩
  case β.β => exact .inr rfl
  case β.app₁ snv _ r =>
    cases r with | lam r =>
    exact .inl ⟨_, .β snv, .subst _ (.once r)⟩
  case β.app₂ snv _ r =>
    cases snv with | sn h =>
    exact .inl ⟨_, .β (h r), r.replace⟩
  case ζ.ζ => exact .inr rfl
  case ζ.letin₁ snv _ r =>
    cases r with | ret r =>
    cases snv with | sn h =>
    exact .inl ⟨_, .ζ (h r), r.replace⟩
  case ζ.letin₂ snv _ r =>
    exact .inl ⟨_, .ζ snv, .subst _ (.once r)⟩
  case ι1.ιl => exact .inr rfl
  case ι1.case snv snn _ r =>
    cases r with | inl r =>
    cases snv with | sn h =>
    exact .inl ⟨_, .ι1 (h r) snn, r.replace⟩
  case ι1.case₁ snv snn _ r =>
    exact .inl ⟨_, .ι1 snv snn, .subst _ (.once r)⟩
  case ι1.case₂ snv snn _ r =>
    cases snn with | sn h =>
    exact .inl ⟨_, .ι1 snv (h r), .refl⟩
  case ι2.ιr => exact .inr rfl
  case ι2.case snv snm _ r =>
    cases r with | inr r =>
    cases snv with | sn h =>
    exact .inl ⟨_, .ι2 (h r) snm, r.replace⟩
  case ι2.case₁ snv snm _ r =>
    cases snm with | sn h =>
    exact .inl ⟨_, .ι2 snv (h r), .refl⟩
  case ι2.case₂ snv snm _ r =>
    exact .inl ⟨_, .ι2 snv snm, .subst _ (.once r)⟩
  case π1.π1 => exact .inr rfl
  case π1.fst snn _ r =>
    cases r
    case prod₁ r => exact .inl ⟨_, .π1 snn, .once r⟩
    case prod₂ n₁ n₂ _ r =>
    cases snn with | sn h =>
    exact .inl ⟨n₁, .π1 (h r), .refl⟩
  case π2.π2 => exact .inr rfl
  case π2.snd snm _ r =>
    cases r
    case prod₂ r => exact .inl ⟨_, .π2 snm, .once r⟩
    case prod₁ n₁ n₂ _ r =>
    cases snm with | sn h =>
    exact .inl ⟨n₂, .π2 (h r), .refl⟩
  case app.β r ih => cases r
  case app.app₁ snv _ ih _ r =>
    match ih r with
    | .inl ⟨_, r₁', r₂'⟩ => exact .inl ⟨_, .app r₁', .app₁ r₂'⟩
    | .inr e => subst e; exact .inr rfl
  case app.app₂ r₁' _ _ r₂' =>
    exact .inl ⟨_, .app r₁', .app₂ (.once r₂')⟩
  case letin.ζ r _ => cases r
  case letin.letin₁ ih _ r =>
    match ih r with
    | .inl ⟨_, r₁', r₂'⟩ => exact .inl ⟨_, .letin r₁', .letin₁ r₂'⟩
    | .inr e => subst e; exact .inr rfl
  case letin.letin₂ r₁ ih _ r₂ =>
    exact .inl ⟨_, .letin r₁, .letin₂ (.once r₂)⟩
  case fst.π1 r _ => cases r
  case fst.fst ih _ r =>
    match ih r with
    | .inl ⟨_, r₁', r₂'⟩ => exact .inl ⟨_, .fst r₁', .fst r₂'⟩
    | .inr e => subst e; exact .inr rfl
  case snd.π2 r _ => cases r
  case snd.snd ih _ r =>
    match ih r with
    | .inl ⟨_, r₁', r₂'⟩ => exact .inl ⟨_, .snd r₁', .snd r₂'⟩
    | .inr e => subst e; exact .inr rfl

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

theorem closure_fst {m n} (r₁ : m ⤳ⁿ n) (snn : StepCom.SN m) (snfst : StepCom.SN (fst n)) : StepCom.SN (fst m) := by
  induction snn generalizing n
  case sn h ih =>
  constructor; intro _ r; cases r
  case a.π1 => cases r₁
  case a.fst r₂ =>
    match confluence r₂ r₁ with
    | .inl ⟨_, r₂', r₁'⟩ => exact ih r₂ r₂' ((StepComs.fst r₁').SN snfst)
    | .inr e => subst e; exact snfst

theorem closure_snd {m n} (r₁ : m ⤳ⁿ n) (snn : StepCom.SN m) (snsnd : StepCom.SN (snd n)) : StepCom.SN (snd m) := by
  induction snn generalizing n
  case sn h ih =>
  constructor; intro _ r; cases r
  case a.π2 => cases r₁
  case a.snd r₂ =>
    match confluence r₂ r₁ with
    | .inl ⟨_, r₂', r₁'⟩ => exact ih r₂ r₂' ((StepComs.snd r₁').SN snsnd)
    | .inr e => subst e; exact snsnd


theorem StepSN.closure {m n} (r : m ⤳ⁿ n) (snn : StepCom.SN n) : StepCom.SN m := by
  induction r
  case π => exact .force_thunk snn
  case β snv => exact .app_lam snv snn
  case ζ snv => exact .letin_ret snv snn
  case ι1 snv snm => exact .case_inl snv snn snm
  case ι2 snv snm => exact .case_inr snv snm snn
  case π1 snm => exact .fst_prod snn snm
  case π2 snm => exact .snd_prod snm snn
  case app rn ih => exact closure_app rn (ih snn.app_inv₁) snn.app_inv₂ snn
  case letin rn ih => exact closure_letin rn (ih snn.letin_inv₁) snn.letin_inv₂ snn
  case fst r ih => exact closure_fst r (ih snn.fst_inv) snn
  case snd r ih => exact closure_snd r (ih snn.snd_inv) snn

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
  | fst m => NeCom m
  | snd m => NeCom m
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

theorem StepCom.SN.prod {m n} (snm : StepCom.SN m) (snn : StepCom.SN n) : StepCom.SN (.prod m n) := by
  induction snm generalizing n
  induction snn
  case sn.sn ihm _ hm ihn =>
  constructor; intro _ r
  cases r
  case a.prod₁ r => exact ihm r (.sn hm)
  case a.prod₂ r => exact ihn r

theorem StepCom.SN.fst {m} (nem : NeCom m) (snm : StepCom.SN m) : StepCom.SN (.fst m) := by
  induction snm
  case sn h ih =>
  constructor; intro _ r
  cases r
  case a.π1 => cases nem
  case a.fst r => exact ih r (r.preservation nem)

theorem StepCom.SN.snd {m} (nem : NeCom m) (snm : StepCom.SN m) : StepCom.SN (.snd m) := by
  induction snm
  case sn h ih =>
  constructor; intro _ r
  cases r
  case a.π2 => cases nem
  case a.snd r => exact ih r (r.preservation nem)
