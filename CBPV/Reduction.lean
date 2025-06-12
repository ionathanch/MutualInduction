import CBPV.RTC
import CBPV.Syntax

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

@[reducible] def StepVals := RTC StepVal
@[reducible] def StepComs := RTC StepCom
infix:40 "⤳⋆ᵛ" => StepVals
infix:40 "⤳⋆ᶜ" => StepComs

/-*---------------------------------
  Renaming and substitution lemmas
  on single-step reduction
---------------------------------*-/

theorem stepRenaming ξ :
  (∀ {v w}, v ⤳ᵛ w → renameVal ξ v ⤳ᵛ renameVal ξ w) ∧
  (∀ {m n}, m ⤳ᶜ n → renameCom ξ m ⤳ᶜ renameCom ξ n) := by
  refine ⟨λ r ↦ ?val, λ r ↦ ?com⟩
  mutual_induction r, r generalizing ξ
  all_goals try rw [← renameDist]
  all_goals constructor
  all_goals apply_assumption

def StepVal.rename {v w} ξ := @(stepRenaming ξ).left v w
def StepCom.rename {m n} ξ := @(stepRenaming ξ).right m n

theorem stepSubstitution σ :
  (∀ {v w}, v ⤳ᵛ w → v⦃σ⦄ ⤳ᵛ w⦃σ⦄) ∧
  (∀ {m n}, m ⤳ᶜ n → m⦃σ⦄ ⤳ᶜ n⦃σ⦄) := by
  refine ⟨λ r ↦ ?val, λ r ↦ ?com⟩
  mutual_induction r, r generalizing σ
  all_goals try rw [← substDist]
  all_goals constructor
  all_goals apply_assumption

def StepVal.subst {v w} σ := @(stepSubstitution σ).left v w
def StepCom.subst {m n} σ := @(stepSubstitution σ).right m n

/-*-----------------------------------------
  Congruence rules on multi-step reduction
-----------------------------------------*-/

theorem StepVals.inl {v w} (r : v ⤳⋆ᵛ w) : inl v ⤳⋆ᵛ inl w := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.inl r₁) r₂

theorem StepVals.inr {v w} (r : v ⤳⋆ᵛ w) : inr v ⤳⋆ᵛ inr w := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.inr r₁) r₂

theorem StepVals.thunk {m n} (r : m ⤳⋆ᶜ n) : thunk m ⤳⋆ᵛ thunk n := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.thunk r₁) r₂

theorem StepComs.force {v w} (r : v ⤳⋆ᵛ w) : force v ⤳⋆ᶜ force w := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.force r₁) r₂

theorem StepComs.ret {v w} (r : v ⤳⋆ᵛ w) : ret v ⤳⋆ᶜ ret w := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.ret r₁) r₂

theorem StepComs.lam {m n} (r : m ⤳⋆ᶜ n) : lam m ⤳⋆ᶜ lam n := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.lam r₁) r₂

theorem StepComs.app₁ {m n v} (r : m ⤳⋆ᶜ n) : app m v ⤳⋆ᶜ app n v := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.app₁ r₁) r₂

theorem StepComs.app₂ {m v w} (r : v ⤳⋆ᵛ w) : app m v ⤳⋆ᶜ app m w := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.app₂ r₁) r₂

theorem StepComs.app {m n v w} (rm : m ⤳⋆ᶜ n) (rv : v ⤳⋆ᵛ w) : app m v ⤳⋆ᶜ app n w :=
  Trans.trans (StepComs.app₁ rm) (StepComs.app₂ rv)

theorem StepComs.letin₁ {m m' n} (r : m ⤳⋆ᶜ m') : letin m n ⤳⋆ᶜ letin m' n := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.letin₁ r₁) r₂

theorem StepComs.letin₂ {m n n'} (r : n ⤳⋆ᶜ n') : letin m n ⤳⋆ᶜ letin m n' := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.letin₂ r₁) r₂

theorem StepComs.letin {m m' n n'} (rm : m ⤳⋆ᶜ m') (rn : n ⤳⋆ᶜ n') : letin m n ⤳⋆ᶜ letin m' n' :=
  Trans.trans (StepComs.letin₁ rm) (StepComs.letin₂ rn)

theorem StepComs.case₀ {v w m n} (r : v ⤳⋆ᵛ w) : case v m n ⤳⋆ᶜ case w m n := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.case r₁) r₂

theorem StepComs.case₁ {v m m' n} (r : m ⤳⋆ᶜ m') : case v m n ⤳⋆ᶜ case v m' n := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.case₁ r₁) r₂

theorem StepComs.case₂ {v m n n'} (r : n ⤳⋆ᶜ n') : case v m n ⤳⋆ᶜ case v m n' := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.case₂ r₁) r₂

theorem StepComs.case {v w m m' n n'} (rv : v ⤳⋆ᵛ w) (rm : m ⤳⋆ᶜ m') (rn : n ⤳⋆ᶜ n') : case v m n ⤳⋆ᶜ case w m' n' :=
  Trans.trans (StepComs.case₀ rv) (Trans.trans (StepComs.case₁ rm) (StepComs.case₂ rn))

/-*--------------------------------------------
  Substitution lemmas on multi-step reduction
--------------------------------------------*-/

theorem StepVals.rename {v w} ξ (r : v ⤳⋆ᵛ w) : renameVal ξ v ⤳⋆ᵛ renameVal ξ w := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.rename ξ r₁) r₂

theorem StepComs.rename {m n} ξ (r : m ⤳⋆ᶜ n) : renameCom ξ m ⤳⋆ᶜ renameCom ξ n := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.rename ξ r₁) r₂

theorem StepVals.subst {v w} (σ : Nat → Val) (r : v ⤳⋆ᵛ w) : v⦃σ⦄ ⤳⋆ᵛ w⦃σ⦄ := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.subst σ r₁) r₂

theorem StepComs.subst {m n} (σ : Nat → Val) (r : m ⤳⋆ᶜ n) : m⦃σ⦄ ⤳⋆ᶜ n⦃σ⦄ := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.subst σ r₁) r₂

theorem StepVals.lift {σ τ} (h : ∀ x, σ x ⤳⋆ᵛ τ x) : ∀ x, (⇑ σ) x ⤳⋆ᵛ (⇑ τ) x := by
  intro n; cases n
  case zero => exact .refl
  case succ n => exact .rename Nat.succ (h n)

theorem stepReplace {σ τ} (h : ∀ x, σ x ⤳⋆ᵛ τ x):
  (∀ {v}, v⦃σ⦄ ⤳⋆ᵛ v⦃τ⦄) ∧
  (∀ {m}, m⦃σ⦄ ⤳⋆ᶜ m⦃τ⦄) := by
  refine ⟨λ {v} ↦ ?val, λ {m} ↦ ?com⟩
  mutual_induction v, m generalizing σ τ
  case var => apply h
  case unit => exact .refl
  case inl ih => exact .inl (ih h)
  case inr ih => exact .inr (ih h)
  case thunk ih => exact .thunk (ih h)
  case force ih => exact .force (ih h)
  case lam ih => exact .lam (ih (.lift h))
  case app ihm ihv => exact .app (ihm h) (ihv h)
  case ret ih => exact .ret (ih h)
  case letin ihm ihn => exact .letin (ihm h) (ihn (.lift h))
  case case ihv ihm ihn => exact .case (ihv h) (ihm (.lift h)) (ihn (.lift h))

theorem StepVal.replace {m : Com} {v w : Val} (r : v ⤳ᵛ w) : m⦃v⦄ ⤳⋆ᶜ m⦃w⦄ := by
  refine @(stepReplace ?ext).right m
  intro n; cases n
  case zero => exact .once r
  case succ => simp; exact .refl
