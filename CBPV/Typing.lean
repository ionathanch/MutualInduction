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

theorem wtRenameCom {ξ} {Γ Δ : Ctxt} {m} {B : ComType} :
  Δ ⊢ ξ ∶ Γ → Γ ⊢ m ∶ B → Δ ⊢ renameCom ξ m ∶ B :=
  λ hξ ↦ (wtRename hξ).right

theorem wtWeakenCom {Γ A B} {m : Com} :
  Γ ⊢ m ∶ B → Γ ∷ A ⊢ renameCom succ m ∶ B :=
  wtRenameCom wRenameSucc

theorem wtWeakenCom₂ {Γ A₁ A₂ B} {m : Com} :
  Γ ∷ A₂ ⊢ m ∶ B → Γ ∷ A₁ ∷ A₂ ⊢ renameCom (lift succ) m ∶ B :=
  wtRenameCom (wRenameLift wRenameSucc)
