import CBPV.Syntax

open Nat ValType ComType Val Com

section
set_option hygiene false
local notation:40 Γ:41 "⊢" v:41 "∶" A:41 => ValWt Γ v A
local notation:40 Γ:41 "⊢" m:41 "∶" B:41 => ComWt Γ m B

mutual
inductive ValWt : Ctxt → Val → ValType → Prop where
  | var {Γ x A} :
    Γ ∋ x ∶ A →
    -------------
    Γ ⊢ var x ∶ A
  | unit {Γ} : Γ ⊢ unit ∶ Unit
  | inl {Γ v} {A₁ A₂ : ValType} :
    Γ ⊢ v ∶ A₁ →
    ---------------------
    Γ ⊢ inl v ∶ Sum A₁ A₂
  | inr {Γ v} {A₁ A₂ : ValType} :
    Γ ⊢ v ∶ A₂ →
    ---------------------
    Γ ⊢ inr v ∶ Sum A₁ A₂
  | thunk {Γ m} {B : ComType} :
    Γ ⊢ m ∶ B →
    -----------------
    Γ ⊢ thunk m ∶ U B

inductive ComWt : Ctxt → Com → ComType → Prop where
  | force {Γ v B} :
    Γ ⊢ v ∶ U B →
    ---------------
    Γ ⊢ force v ∶ B
  | lam {Γ m A} {B : ComType} :
    Γ ∷ A ⊢ m ∶ B →
    -------------------
    Γ ⊢ lam m ∶ Arr A B
  | app {Γ m v A B} :
    Γ ⊢ m ∶ Arr A B →
    Γ ⊢ v ∶ A →
    ---------------
    Γ ⊢ app m v ∶ B
  | ret {Γ v} {A : ValType} :
    Γ ⊢ v ∶ A →
    ---------------
    Γ ⊢ ret v ∶ F A
  | letin {Γ m n A} {B : ComType} :
    Γ ⊢ m ∶ F A →
    Γ ∷ A ⊢ n ∶ B →
    -----------------
    Γ ⊢ letin m n ∶ B
  | case {Γ v m n A₁ A₂} {B : ComType} :
    Γ ⊢ v ∶ Sum A₁ A₂ →
    Γ ∷ A₁ ⊢ m ∶ B →
    Γ ∷ A₂ ⊢ n ∶ B →
    ------------------
    Γ ⊢ case v m n ∶ B
  | prod {Γ m n} {B₁ B₂: ComType} :
    Γ ⊢ m ∶ B₁ →
    Γ ⊢ n ∶ B₂ →
    -------------------------
    Γ ⊢ prod m n ∶ Prod B₁ B₂
  | fst {Γ m} {B₁ B₂ : ComType} :
    Γ ⊢ m ∶ Prod B₁ B₂ →
    --------------------
    Γ ⊢ fst m ∶ B₁
  | snd {Γ m} {B₁ B₂ : ComType} :
    Γ ⊢ m ∶ Prod B₁ B₂ →
    --------------------
    Γ ⊢ snd m ∶ B₂
end
end

notation:40 Γ:41 "⊢" v:41 "∶" A:41 => ValWt Γ v A
notation:40 Γ:41 "⊢" m:41 "∶" B:41 => ComWt Γ m B

/-*------------------------------
  Renaming and weakening lemmas
------------------------------*-/

theorem wtRename {ξ} {Γ Δ : Ctxt} (hξ : Δ ⊢ ξ ∶ Γ) :
  (∀ {v} {A : ValType}, Γ ⊢ v ∶ A → Δ ⊢ renameVal ξ v ∶ A) ∧
  (∀ {m} {B : ComType}, Γ ⊢ m ∶ B → Δ ⊢ renameCom ξ m ∶ B) := by
  refine ⟨λ h ↦ ?wtv, λ h ↦ ?wtm⟩
  mutual_induction h, h generalizing ξ Δ
  all_goals constructor <;> apply_rules [wRenameLift]

theorem wtRenameVal {ξ} {Γ Δ : Ctxt} {v} {A : ValType} :
  Δ ⊢ ξ ∶ Γ → Γ ⊢ v ∶ A → Δ ⊢ renameVal ξ v ∶ A :=
  λ hξ ↦ (wtRename hξ).left

theorem wtRenameCom {ξ} {Γ Δ : Ctxt} {m} {B : ComType} :
  Δ ⊢ ξ ∶ Γ → Γ ⊢ m ∶ B → Δ ⊢ renameCom ξ m ∶ B :=
  λ hξ ↦ (wtRename hξ).right

theorem wtWeakenVal {Γ A₁ A₂} {v : Val} :
  Γ ⊢ v ∶ A₂ → Γ ∷ A₁ ⊢ renameVal succ v ∶ A₂ :=
    wtRenameVal wRenameSucc

theorem wtWeakenCom {Γ A B} {m : Com} :
  Γ ⊢ m ∶ B → Γ ∷ A ⊢ renameCom succ m ∶ B :=
  wtRenameCom wRenameSucc

theorem wtWeakenCom₂ {Γ A₁ A₂ B} {m : Com} :
  Γ ∷ A₂ ⊢ m ∶ B → Γ ∷ A₁ ∷ A₂ ⊢ renameCom (lift succ) m ∶ B :=
  wtRenameCom (wRenameLift wRenameSucc)

/-*--------------------------------------
  Rearrangement lemmas for commutations
--------------------------------------*-/

theorem wtLetApp {Γ n m v A B} (hlet : Γ ⊢ letin n m ∶ Arr A B) (hv : Γ ⊢ v ∶ A) :
  Γ ⊢ letin n (app m (renameVal succ v)) ∶ B := by
  cases hlet with | letin hn hm =>
  exact .letin hn (.app hm (wtWeakenVal hv))

theorem wtLetFst {Γ n m B₁ B₂} (hlet : Γ ⊢ letin n m ∶ Prod B₁ B₂) :
  Γ ⊢ letin n (fst m) ∶ B₁ := by
  cases hlet with | letin hn hm =>
  exact .letin hn (.fst hm)

theorem wtLetSnd {Γ n m B₁ B₂} (hlet : Γ ⊢ letin n m ∶ Prod B₁ B₂) :
  Γ ⊢ letin n (snd m) ∶ B₂ := by
  cases hlet with | letin hn hm =>
  exact .letin hn (.snd hm)

theorem wtCaseApp {Γ v m₁ m₂ w A B} (hcase : Γ ⊢ case v m₁ m₂ ∶ Arr A B) (hw : Γ ⊢ w ∶ A) :
  Γ ⊢ case v (app m₁ (renameVal succ w)) (app m₂ (renameVal succ w)) ∶ B := by
  cases hcase with | case hv hm₁ hm₂ =>
  exact .case hv (.app hm₁ (wtWeakenVal hw)) (.app hm₂ (wtWeakenVal hw))

theorem wtCaseFst {Γ v m₁ m₂ B₁ B₂} (hcase : Γ ⊢ case v m₁ m₂ ∶ Prod B₁ B₂) :
  Γ ⊢ case v (fst m₁) (fst m₂) ∶ B₁ := by
  cases hcase with | case hv hm₁ hm₂ =>
  exact .case hv (.fst hm₁) (.fst hm₂)

theorem wtCaseSnd {Γ v m₁ m₂ B₁ B₂} (hcase : Γ ⊢ case v m₁ m₂ ∶ Prod B₁ B₂) :
  Γ ⊢ case v (snd m₁) (snd m₂) ∶ B₂ := by
  cases hcase with | case hv hm₁ hm₂ =>
  exact .case hv (.snd hm₁) (.snd hm₂)
