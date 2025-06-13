import CBPV.NormalInd

open Val Com

/-*-----------------------------------------
  Not a lambda/return/product/inl/inr
  (to restrict reduction in head position)
-----------------------------------------*-/

@[simp, reducible]
def NotLamRetProd : Com → Prop
  | lam _ | ret _ | prod _ _ => False
  | _ => True

@[simp, reducible]
def NotInlr : Val → Prop
  | inl _ | inr _ => False
  | _ => True

/-*-------------------------
  Neutral and normal forms
-------------------------*-/

def NeVal (v : Val) : Prop := ∃ x, v = var x

mutual
inductive NeCom : Com → Prop where
  | force {x} : NeCom (force (var x))
  | app {m v} : NeCom m → NfVal v → NeCom (app m v)
  | letin {m n} : NeCom m → NfCom n → NeCom (letin m n)
  | case {x m n} : NfCom m → NfCom n → NeCom (case (var x) m n)
  | fst {m} : NeCom m → NeCom (fst m)
  | snd {m} : NeCom m → NeCom (snd m)

inductive NfVal : Val → Prop where
  | var {x} : NfVal (var x)
  | unit : NfVal unit
  | inl {v} : NfVal v → NfVal (inl v)
  | inr {v} : NfVal v → NfVal (inr v)
  | thunk {m} : NfCom m → NfVal (thunk m)

inductive NfCom : Com → Prop where
  | lam {m} : NfCom m → NfCom (lam m)
  | ret {v} : NfVal v → NfCom (ret v)
  | prod {m n} : NfCom m → NfCom n → NfCom (prod m n)
  | ne {m} : NeCom m → NfCom m
end

theorem NeCom.NotLamRetProd {m} (nem : NeCom m) : NotLamRetProd m := by
  cases nem <;> simp

/-*-----------------------------
  Leftmost outermost reduction
-----------------------------*-/

section
set_option hygiene false
local infix:40 "⤳ᵛ" => RedVal
local infix:40 "⤳ᶜ" => RedCom

mutual
inductive RedVal : Val → Val → Prop where
  | inl {v w} : v ⤳ᵛ w → inl v ⤳ᵛ inl w
  | inr {v w} : v ⤳ᵛ w → inr v ⤳ᵛ inr w
  | thunk {m n} : m ⤳ᶜ n → thunk m ⤳ᵛ thunk n

inductive RedCom : Com → Com → Prop where
  | π {m} : force (thunk m) ⤳ᶜ m
  | β {m v} : app (lam m) v ⤳ᶜ m⦃v⦄
  | ζ {v m} : letin (ret v) m ⤳ᶜ m⦃v⦄
  | ιl {v m n} : case (inl v) m n ⤳ᶜ m⦃v⦄
  | ιr {v m n} : case (inr v) m n ⤳ᶜ n⦃v⦄
  | π1 {m n} : fst (prod m n) ⤳ᶜ m
  | π2 {m n} : snd (prod m n) ⤳ᶜ n
  | lam {m n} : m ⤳ᶜ n → lam m ⤳ᶜ lam n
  | app₁ {m n v} : NotLamRetProd m → m ⤳ᶜ n → app m v ⤳ᶜ app n v
  | app₂ {m v w} : NeCom m → v ⤳ᵛ w → app m v ⤳ᶜ app m w
  | ret {v w} : v ⤳ᵛ w → ret v ⤳ᶜ ret w
  | prod₁ {m m' n} : m ⤳ᶜ m' → prod m n ⤳ᶜ prod m' n
  | prod₂ {m n n'} : NfCom m → n ⤳ᶜ n' → prod m n ⤳ᶜ prod m n'
  | letin₁ {m m' n} : NotLamRetProd m → m ⤳ᶜ m' → letin m n ⤳ᶜ letin m' n
  | letin₂ {m n n'} : NeCom m → n ⤳ᶜ n' → letin m n ⤳ᶜ letin m n'
  | case₀ {v w m n} : NotInlr v → v ⤳ᵛ w → case v m n ⤳ᶜ case w m n
  | case₁ {x m m' n} : m ⤳ᶜ m' → case (var x) m n ⤳ᶜ case (var x) m' n
  | case₂ {x m n n'} : NfCom m → n ⤳ᶜ n' → case (var x) m n ⤳ᶜ case (var x) m n'
  | fst {m m'} : NotLamRetProd m → m ⤳ᶜ m' → fst m ⤳ᶜ fst m'
  | snd {m m'} : NotLamRetProd m → m ⤳ᶜ m' → snd m ⤳ᶜ snd m'
end
end

infix:40 "⤳ᵛ" => RedVal
infix:40 "⤳ᶜ" => RedCom

@[reducible] def RedVals := RTC RedVal
@[reducible] def RedComs := RTC RedCom

infix:40 "⤳⋆ᵛ" => RedVals
infix:40 "⤳⋆ᶜ" => RedComs

/-*--------------------------------------------
  Properties of leftmost outermost reduction:
  * Neutral and normal forms don't reduce
  * Reduction is deterministic
--------------------------------------------*-/

theorem normality :
  (∀ {m n}, NeCom m → m ⤳ᶜ n → False) ∧
  (∀ {v w}, NfVal v → v ⤳ᵛ w → False) ∧
  (∀ {m n}, NfCom m → m ⤳ᶜ n → False) := by
  refine ⟨λ nem r ↦ ?necom, λ nfv r ↦ ?nfval, λ nfm r ↦ ?nfcom⟩
  mutual_induction nem, nfv, nfm
  case ne ih _ => exact ih r
  case force | var | unit => cases r
  case inl ih _ | inr ih _ | thunk ih _ | lam ih _ | ret ih _ =>
    cases r; rename_i r; exact ih r
  case app ihm ihv _ =>
    cases r
    case β nelam => cases nelam
    case app₁ r => exact ihm r
    case app₂ r => exact ihv r
  case letin ihm ihn _ =>
    cases r
    case ζ neret => cases neret
    case letin₁ r => exact ihm r
    case letin₂ r => exact ihn r
  case case ihm ihn _ =>
    cases r
    case case₀ r => cases r
    case case₁ r => exact ihm r
    case case₂ r => exact ihn r
  case fst neprod _ _ =>
    cases r
    case π1 => cases neprod
    case fst ih _ _ r => exact ih r
  case snd neprod _ _ =>
    cases r
    case π2 => cases neprod
    case snd ih _ _ r => exact ih r
  case prod ihm ihn _ =>
    cases r
    case prod₁ r => exact ihm r
    case prod₂ r => exact ihn r

def NeCom.normality {m n} := @_root_.normality.left m n
def NfVal.normality {v w} := @_root_.normality.right.left v w
def NfCom.normality {m n} := @_root_.normality.right.right m n

theorem determinism :
  (∀ {v w w'}, v ⤳ᵛ w → v ⤳ᵛ w' → w = w') ∧
  (∀ {m n n'}, m ⤳ᶜ n → m ⤳ᶜ n' → n = n') := by
  refine ⟨λ r₁ r₂ ↦ ?val, λ r₁ r₂ ↦ ?com⟩
  mutual_induction r₁, r₁
  case inl r ih _ => cases r₂ with | _ r₂ => rw [ih r₂]
  case inr r ih _ => cases r₂ with | _ r₂ => rw [ih r₂]
  case thunk r ih _ => cases r₂ with | _ r₂ => rw [ih r₂]
  case π => cases r₂; rfl
  case β =>
    cases r₂
    case β => rfl
    case app₁ => contradiction
    case app₂ nelam _ => cases nelam
  case ζ =>
    cases r₂; rfl; contradiction
    case letin₂ neret _ => cases neret
  case ιl => cases r₂; rfl; contradiction
  case ιr => cases r₂; rfl; contradiction
  case π1 => cases r₂; rfl; contradiction
  case π2 => cases r₂; rfl; contradiction
  case lam ih _ => cases r₂ with | lam r => rw [ih r]
  case app₁ ih _ =>
    cases r₂; contradiction
    case app₁ r => rw [ih r]
    case app₂ r _ nem _ => cases nem.normality r
  case app₂ ih _ =>
    cases r₂; contradiction
    case app₁ nem _ _ _ r => cases nem.normality r
    case app₂ r => rw [ih r]
  case ret ih _ => cases r₂ with | ret r => rw [ih r]
  case prod₁ ih _ =>
    cases r₂
    case prod₁ r => rw [ih r]
    case prod₂ r _ nfm _ => cases nfm.normality r
  case prod₂ ih _ =>
    cases r₂
    case prod₁ nfm _ _ r => cases nfm.normality r
    case prod₂ r => rw [ih r]
  case letin₁ ih _ =>
    cases r₂; contradiction
    case letin₁ r => rw [ih r]
    case letin₂ r _ nem _ => cases nem.normality r
  case letin₂ ih _ =>
    cases r₂; contradiction
    case letin₁ nem _ _ _ r => cases nem.normality r
    case letin₂ r => rw [ih r]
  case case₀ ih _ =>
    cases r₂; contradiction; contradiction
    case case₀ r => rw [ih r]
    case case₁ r _ => cases r
    case case₂ r _ _ => cases r
  case case₁ ih _ =>
    cases r₂
    case case₀ r => cases r
    case case₁ r => rw [ih r]
    case case₂ r _ nfm _ => cases nfm.normality r
  case case₂ ih _ =>
    cases r₂
    case case₀ r => cases r
    case case₁ nfm _ _ r => cases nfm.normality r
    case case₂ r => rw [ih r]
  case fst ih _ =>
    cases r₂; contradiction
    case fst r => rw [ih r]
  case snd ih _ =>
    cases r₂; contradiction
    case snd r => rw [ih r]

/-*---------------------------------------
  Backward closure of nonconstructorness
---------------------------------------*-/

theorem RedCom.notLamRetProd {m n} (r : m ⤳ᶜ n) (nl : NotLamRetProd n) : NotLamRetProd m := by
  mutual_induction r generalizing nl <;> simp at *

theorem RedVal.notInlr {v w} (r : v ⤳ᵛ w) (ni : NotInlr w) : NotInlr v := by
  mutual_induction r generalizing ni <;> simp at *

theorem RedComs.notLamRetProd {m n} (r : m ⤳⋆ᶜ n) (nl : NotLamRetProd n) : NotLamRetProd m := by
  induction r
  case refl => exact nl
  case trans r _ ih => exact r.notLamRetProd (ih nl)

theorem RedVals.notInlr {v w} (r : v ⤳⋆ᵛ w) (ni : NotInlr w) : NotInlr v := by
  induction r
  case refl => exact ni
  case trans r _ ih => exact r.notInlr (ih ni)

/-*------------------------------------------
  Congruence rules for multi-step reduction
------------------------------------------*-/

theorem RedVals.inl {v w} (r : v ⤳⋆ᵛ w) : inl v ⤳⋆ᵛ inl w := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.inl r₁) r₂

theorem RedVals.inr {v w} (r : v ⤳⋆ᵛ w) : inr v ⤳⋆ᵛ inr w := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.inr r₁) r₂

theorem RedVals.thunk {m n} (r : m ⤳⋆ᶜ n) : thunk m ⤳⋆ᵛ thunk n := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.thunk r₁) r₂

theorem RedComs.ret {v w} (r : v ⤳⋆ᵛ w) : ret v ⤳⋆ᶜ ret w := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.ret r₁) r₂

theorem RedComs.lam {m n} (r : m ⤳⋆ᶜ n) : lam m ⤳⋆ᶜ lam n := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.lam r₁) r₂

theorem RedComs.app₁ {m n v} (nl : NotLamRetProd n) (r : m ⤳⋆ᶜ n) : app m v ⤳⋆ᶜ app n v := by
  induction r
  case refl => exact .refl
  case trans r₁ r₂ ih => exact .trans (.app₁ (RedComs.notLamRetProd (.trans r₁ r₂) nl) r₁) (ih nl)

theorem RedComs.app₂ {m v w} (nem : NeCom m) (r : v ⤳⋆ᵛ w) : app m v ⤳⋆ᶜ app m w := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.app₂ nem r₁) r₂

theorem RedComs.letin₁ {m m' n} (nr : NotLamRetProd m') (r : m ⤳⋆ᶜ m') : letin m n ⤳⋆ᶜ letin m' n := by
  induction r
  case refl => exact .refl
  case trans r₁ r₂ ih => exact .trans (.letin₁ (RedComs.notLamRetProd (.trans r₁ r₂) nr) r₁) (ih nr)

theorem RedComs.letin₂ {m n n'} (nem : NeCom m) (r : n ⤳⋆ᶜ n') : letin m n ⤳⋆ᶜ letin m n' := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.letin₂ nem r₁) r₂

theorem RedComs.case₀ {v w m n} (ni : NotInlr w) (r : v ⤳⋆ᵛ w) : case v m n ⤳⋆ᶜ case w m n := by
  induction r
  case refl => exact .refl
  case trans r₁ r₂ ih => exact .trans (.case₀ (RedVals.notInlr (.trans r₁ r₂) ni) r₁) (ih ni)

theorem RedComs.case₁ {x m m' n} (r : m ⤳⋆ᶜ m') : case (var x) m n ⤳⋆ᶜ case (var x) m' n := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.case₁ r₁) r₂

theorem RedComs.case₂ {x m n n'} (nem : NfCom m) (r : n ⤳⋆ᶜ n') : case (var x) m n ⤳⋆ᶜ case (var x) m n' := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.case₂ nem r₁) r₂

theorem RedComs.prod₁ {m m' n} (r : m ⤳⋆ᶜ m') : prod m n ⤳⋆ᶜ prod m' n := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.prod₁ r₁) r₂

theorem RedComs.prod₂ {m n n'} (nfm : NfCom m) (r : n ⤳⋆ᶜ n') : prod m n ⤳⋆ᶜ prod m n' := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.prod₂ nfm r₁) r₂

theorem RedComs.prod {m m' n n'} (nfm : NfCom m') (rm : m ⤳⋆ᶜ m') (rn : n ⤳⋆ᶜ n') : prod m n ⤳⋆ᶜ prod m' n' :=
  Trans.trans (RedComs.prod₁ rm) (RedComs.prod₂ nfm rn)

theorem RedComs.fst {m m'} (np : NotLamRetProd m') (r : m ⤳⋆ᶜ m') : fst m ⤳⋆ᶜ fst m' := by
  induction r
  case refl => exact .refl
  case trans r₁ r₂ ih => exact .trans (.fst (RedComs.notLamRetProd (.trans r₁ r₂) np) r₁) (ih np)

theorem RedComs.snd {m m'} (np : NotLamRetProd m') (r : m ⤳⋆ᶜ m') : snd m ⤳⋆ᶜ snd m' := by
  induction r
  case refl => exact .refl
  case trans r₁ r₂ ih => refine .trans (.snd (RedComs.notLamRetProd (.trans r₁ r₂) np) r₁) (ih np)

/-*----------------------------------------
  Leftmost outermost reduction normalizes
  strongly normal terms to normal forms
----------------------------------------*-/

theorem SR.NotLamRetProd {m n} (r : m ⤳ n) : NotLamRetProd m := by
  mutual_induction r <;> simp

theorem normalization :
  (∀ {m}, SNeCom m → ∃ n, m ⤳⋆ᶜ n ∧ NeCom n) ∧
  (∀ {v}, SNVal v → ∃ w, v ⤳⋆ᵛ w ∧ NfVal w) ∧
  (∀ {m}, SNCom m → ∃ n, m ⤳⋆ᶜ n ∧ NfCom n) ∧
  (∀ {m n}, m ⤳ n → m ⤳ᶜ n) := by
  refine ⟨λ sne ↦ ?snecom, λ sn ↦ ?snval, λ sn ↦ ?sncom, λ r ↦ ?srcom⟩
  mutual_induction sne, sn, sn, r
  case snecom.force snev =>
    let ⟨_, e⟩ := snev; subst e
    exact ⟨_, .refl, .force⟩
  case snecom.app ihm ihv =>
    let ⟨_, rm, nem⟩ := ihm
    let ⟨_, rv, nfv⟩ := ihv
    exact ⟨_, Trans.trans (RedComs.app₁ (nem.NotLamRetProd) rm) (RedComs.app₂ nem rv), .app nem nfv⟩
  case snecom.letin ihm ihn =>
    let ⟨_, rm, nem⟩ := ihm
    let ⟨_, rn, nfn⟩ := ihn
    exact ⟨_, Trans.trans (RedComs.letin₁ (nem.NotLamRetProd) rm) (RedComs.letin₂ nem rn), .letin nem nfn⟩
  case snecom.case snev _ _ ihm ihn =>
    let ⟨_, e⟩ := snev; subst e
    let ⟨_, rm, nfm⟩ := ihm
    let ⟨_, rn, nfn⟩ := ihn
    exact ⟨_, Trans.trans (RedComs.case₁ rm) (RedComs.case₂ nfm rn), .case nfm nfn⟩
  case snecom.fst ih =>
    let ⟨_, rm, nem⟩ := ih
    exact ⟨_, .fst (nem.NotLamRetProd) rm, .fst nem⟩
  case snecom.snd ih =>
    let ⟨_, rm, nem⟩ := ih
    exact ⟨_, .snd (nem.NotLamRetProd) rm, .snd nem⟩
  case snval.var => exact ⟨_, .refl, .var⟩
  case snval.unit => exact ⟨_, .refl, .unit⟩
  case snval.inl ih =>
    let ⟨_, r, nfv⟩ := ih
    exact ⟨_, .inl r, .inl nfv⟩
  case snval.inr ih =>
    let ⟨_, r, nfv⟩ := ih
    exact ⟨_, .inr r, .inr nfv⟩
  case snval.thunk ih =>
    let ⟨_, r, nfm⟩ := ih
    exact ⟨_, .thunk r, .thunk nfm⟩
  case sncom.lam ih =>
    let ⟨_, r, nfm⟩ := ih
    exact ⟨_, .lam r, .lam nfm⟩
  case sncom.ret ih =>
    let ⟨_, r, nfv⟩ := ih
    exact ⟨_, .ret r, .ret nfv⟩
  case sncom.prod ihm ihn =>
    let ⟨_, rm, nfm⟩ := ihm
    let ⟨_, rn, nfn⟩ := ihn
    exact ⟨_, .prod nfm rm rn, .prod nfm nfn⟩
  case sncom.ne ih =>
    let ⟨_, r, nfm⟩ := ih
    exact ⟨_, r, .ne nfm⟩
  case sncom.red r ih =>
    let ⟨_, r', nfn⟩ := ih
    exact ⟨_, .trans r r', nfn⟩
  case srcom.π => exact .π
  case srcom.β => exact .β
  case srcom.ζ => exact .ζ
  case srcom.ι1 => exact .ιl
  case srcom.ι2 => exact .ιr
  case srcom.π1 => exact .π1
  case srcom.π2 => exact .π2
  case srcom.app sr r => exact .app₁ sr.NotLamRetProd r
  case srcom.letin sr r => exact .letin₁ sr.NotLamRetProd r
  case srcom.fst sr r => exact .fst sr.NotLamRetProd r
  case srcom.snd sr r => exact .snd sr.NotLamRetProd r
