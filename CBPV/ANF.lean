import CBPV.CK
import CBPV.Typing

open Nat ValType ComType
open CK renaming K → S, renameK → renameS

/-*--------------------------------
  A-normal form of CBPV language:
  syntax and typing
--------------------------------*-/

namespace ANF

/-* Values, computations, and configurations *-/

mutual
inductive Val : Type where
  | var : Nat → Val
  | unit : Val
  | inl : Val → Val
  | inr : Val → Val
  | thunk : Cfg → Val

inductive Com : Type where
  | force : Val → Com
  | lam : Cfg → Com
  | app : Com → Val → Com
  | ret : Val → Com
  | prod : Cfg → Cfg → Com
  | fst : Com → Com
  | snd : Com → Com

inductive Cfg : Type where
  | com : Com → Cfg
  | letin : Com → Cfg → Cfg
  | case : Val → Cfg → Cfg → Cfg
end
open Val Com Cfg

/-* Renaming *-/

mutual
@[simp]
def renameVal (ξ : Nat → Nat) : Val → Val
  | var s => var (ξ s)
  | unit => unit
  | inl v => inl (renameVal ξ v)
  | inr v => inr (renameVal ξ v)
  | thunk m => thunk (renameCfg ξ m)

@[simp]
def renameCom (ξ : Nat → Nat) : Com → Com
  | force v => force (renameVal ξ v)
  | lam m => lam (renameCfg (lift ξ) m)
  | app n v => app (renameCom ξ n) (renameVal ξ v)
  | ret v => ret (renameVal ξ v)
  | prod m₁ m₂ => prod (renameCfg ξ m₁) (renameCfg ξ m₂)
  | fst n => fst (renameCom ξ n)
  | snd n => snd (renameCom ξ n)

@[simp]
def renameCfg (ξ : Nat → Nat) : Cfg → Cfg
  | com n => com (renameCom ξ n)
  | letin n m => letin (renameCom ξ n) (renameCfg (lift ξ) m)
  | case v m₁ m₂ => case (renameVal ξ v) (renameCfg (lift ξ) m₁) (renameCfg (lift ξ) m₂)
end

theorem renameExt {ξ ζ} (h : ∀ x, ξ x = ζ x) :
  (∀ v, renameVal ξ v = renameVal ζ v) ∧
  (∀ n, renameCom ξ n = renameCom ζ n) ∧
  (∀ m, renameCfg ξ m = renameCfg ζ m) := by
  refine ⟨λ v ↦ ?val, λ n ↦ ?com, λ m ↦ ?cfg⟩
  mutual_induction v, n, m generalizing ξ ζ
  all_goals simp; try repeat' constructor
  all_goals apply_rules [liftExt]

def renameValExt {ξ ζ : Nat → Nat} {v} (h : ∀ x, ξ x = ζ x) := (renameExt h).left v
def renameCfgExt {ξ ζ : Nat → Nat} {m} (h : ∀ x, ξ x = ζ x) := (renameExt h).right.right m

theorem renameComp {ξ ζ ς} (h : ∀ x, (ξ ∘ ζ) x = ς x) :
  (∀ v, (renameVal ξ ∘ renameVal ζ) v = renameVal ς v) ∧
  (∀ n, (renameCom ξ ∘ renameCom ζ) n = renameCom ς n) ∧
  (∀ m, (renameCfg ξ ∘ renameCfg ζ) m = renameCfg ς m) := by
  refine ⟨λ v ↦ ?val, λ n ↦ ?com, λ m ↦ ?cfg⟩
  mutual_induction v, n, m generalizing ξ ζ ς
  all_goals simp; try repeat' constructor
  all_goals apply_rules [liftComp]

def renameValComp {ξ ζ ς : Nat → Nat} {v} (h : ∀ x, (ξ ∘ ζ) x = ς x) := (renameComp h).left v
def renameCfgComp {ξ ζ ς : Nat → Nat} {v} (h : ∀ x, (ξ ∘ ζ) x = ς x) := (renameComp h).right.right v

/-* Substitution *-/

@[simp]
def up (σ : Nat → Val) : Nat → Val :=
  var 0 +: (renameVal succ ∘ σ)
prefix:95 "⇑" => up

theorem upId (σ : Nat → Val) (h : ∀ x, σ x = var x) : ∀ x, (⇑ σ) x = var x := by
  intro n; cases n <;> simp [h]

theorem upExt (σ τ : Nat → Val) (h : ∀ x, σ x = τ x) : ∀ x, (⇑ σ) x = (⇑ τ) x := by
  intro n; cases n <;> simp [h]

theorem upLift ξ (σ τ : Nat → Val) (h : ∀ x, (σ ∘ ξ) x = τ x) : ∀ x, (⇑ σ ∘ lift ξ) x = (⇑ τ) x := by
  intro n; cases n <;> simp [← h]

theorem upSucc (σ : Nat → Val) : ∀ x, (⇑ σ ∘ succ) x = (renameVal succ ∘ σ) x := by
  intro n; cases n <;> simp

theorem upRename ξ (σ τ : Nat → Val) (h : ∀ x, (renameVal ξ ∘ σ) x = τ x) : ∀ x, (renameVal (lift ξ) ∘ ⇑ σ) x = (⇑ τ) x := by
  intro n; cases n; simp
  case succ n => calc
    (renameVal (lift ξ) ∘ renameVal succ) (σ n)
      = renameVal (lift ξ ∘ succ) (σ n)      := by rw [renameValComp (λ _ ↦ rfl)]
    _ = (renameVal (succ ∘ ξ)) (σ n)         := by rfl
    _ = (renameVal succ ∘ renameVal ξ) (σ n) := by rw [renameValComp (λ _ ↦ rfl)]
    _ = (renameVal succ (renameVal ξ (σ n))) := by rfl
    _ = renameVal succ (τ n)                 := by rw [← h]; rfl

mutual
@[simp]
def substVal (σ : Nat → Val) : Val → Val
  | var x => σ x
  | unit => unit
  | inl v => inl (substVal σ v)
  | inr v => inr (substVal σ v)
  | thunk m => thunk (substCfg σ m)

@[simp]
def substCom (σ : Nat → Val) : Com → Com
  | force v => force (substVal σ v)
  | lam m => lam (substCfg (⇑ σ) m)
  | app n v => app (substCom σ n) (substVal σ v)
  | ret v => ret (substVal σ v)
  | prod m₁ m₂ => prod (substCfg σ m₁) (substCfg σ m₂)
  | fst n => fst (substCom σ n)
  | snd n => snd (substCom σ n)

@[simp]
def substCfg (σ : Nat → Val) : Cfg → Cfg
  | com n => com (substCom σ n)
  | letin n m => letin (substCom σ n) (substCfg (⇑ σ) m)
  | case v m₁ m₂ => case (substVal σ v) (substCfg (⇑ σ) m₁) (substCfg (⇑ σ) m₂)
end

theorem substId σ (h : ∀ x, σ x = var x) :
  (∀ v, substVal σ v = v) ∧
  (∀ n, substCom σ n = n) ∧
  (∀ m, substCfg σ m = m) := by
  refine ⟨λ v ↦ ?val, λ n ↦ ?com, λ m ↦ ? cfg⟩
  mutual_induction v, n, m generalizing σ
  all_goals simp; try repeat' constructor
  all_goals apply_rules [upId]

def substValId := (substId var (λ _ ↦ rfl)).left
def substCfgId := (substId var (λ _ ↦ rfl)).right.right

theorem substExt {σ τ} (h : ∀ x, σ x = τ x) :
  (∀ v, substVal σ v = substVal τ v) ∧
  (∀ n, substCom σ n = substCom τ n) ∧
  (∀ m, substCfg σ m = substCfg τ m) := by
  refine ⟨λ v ↦ ?val, λ n ↦ ?com, λ m ↦ ?cfg⟩
  mutual_induction v, n, m generalizing σ τ
  all_goals simp; try repeat' constructor
  all_goals apply_rules [upExt]

def substValExt {σ τ : Nat → Val} {v} (h : ∀ x, σ x = τ x) := (substExt h).left v
def substCfgExt {σ τ : Nat → Val} {m} (h : ∀ x, σ x = τ x) := (substExt h).right.right m

theorem substRename {ξ σ τ} (h : ∀ x, (σ ∘ ξ) x = τ x) :
  (∀ v, substVal σ (renameVal ξ v) = substVal τ v) ∧
  (∀ n, substCom σ (renameCom ξ n) = substCom τ n) ∧
  (∀ m, substCfg σ (renameCfg ξ m) = substCfg τ m) := by
  refine ⟨λ v ↦ ?val, λ n ↦ ?com, λ m ↦ ?cfg⟩
  mutual_induction v, n, m generalizing ξ σ τ
  all_goals simp; try repeat' constructor
  all_goals apply_rules [upLift]

def substRenameVal {ξ} {σ τ : Nat → Val} {v} (h : ∀ x, (σ ∘ ξ) x = τ x) := (substRename h).left v
def substRenameCfg {ξ} {σ τ : Nat → Val} {m} (h : ∀ x, (σ ∘ ξ) x = τ x) := (substRename h).right.right m

theorem renameSubst {ξ σ τ} (h : ∀ x, (renameVal ξ ∘ σ) x = τ x) :
  (∀ v, renameVal ξ (substVal σ v) = substVal τ v) ∧
  (∀ n, renameCom ξ (substCom σ n) = substCom τ n) ∧
  (∀ m, renameCfg ξ (substCfg σ m) = substCfg τ m) := by
  refine ⟨λ v ↦ ?val, λ n ↦ ?com, λ m ↦ ?cfg⟩
  mutual_induction v, n, m generalizing ξ σ τ
  all_goals simp; try repeat' constructor
  all_goals apply_rules [upRename]

def renameSubstVal {ξ} {σ τ : Nat → Val} {v} (h : ∀ x, (renameVal ξ ∘ σ) x = τ x) := (renameSubst h).left v
def renameSubstCfg {ξ} {σ τ : Nat → Val} {m} (h : ∀ x, (renameVal ξ ∘ σ) x = τ x) := (renameSubst h).right.right m

theorem upSubst (ρ σ τ : Nat → Val) (h : ∀ x, (substVal ρ ∘ σ) x = τ x) :
  (∀ x, (substVal (⇑ ρ) ∘ (⇑ σ)) x = (⇑ τ) x) := by
  intro n; cases n; rfl
  case succ n => calc
    (substVal (⇑ ρ) ∘ renameVal succ) (σ n)
    _ = substVal (⇑ ρ ∘ succ) (σ n)         := by simp [← substRenameVal (λ _ ↦ rfl)]
    _ = substVal (renameVal succ ∘ ρ) (σ n) := by rfl
    _ = (renameVal succ ∘ substVal ρ) (σ n) := by simp [← renameSubstVal (λ _ ↦ rfl)]
    _ = renameVal succ (substVal ρ (σ n))   := by rfl
    _ = renameVal succ (τ n)                := by rw [← h]; rfl

theorem substComp {ρ σ τ} (h : ∀ x, (substVal ρ ∘ σ) x = τ x) :
  (∀ v, (substVal ρ ∘ substVal σ) v = substVal τ v) ∧
  (∀ n, (substCom ρ ∘ substCom σ) n = substCom τ n) ∧
  (∀ m, (substCfg ρ ∘ substCfg σ) m = substCfg τ m) := by
  refine ⟨λ v ↦ ?val, λ n ↦ ?com, λ m ↦ ?cfg⟩
  mutual_induction v, n, m generalizing ρ σ τ
  all_goals simp; try repeat' constructor
  all_goals apply_rules [upSubst]

def substValComp {ρ σ τ : Nat → Val} {v} (h : ∀ x, (substVal ρ ∘ σ) x = τ x) := (substComp h).left v
def substCfgComp {ρ σ τ : Nat → Val} {v} (h : ∀ x, (substVal ρ ∘ σ) x = τ x) := (substComp h).right.right v

/-* Typing *-/

section
set_option hygiene false
local notation:40 Γ:41 "⊢ₐ" v:41 "∶" A:41 => ValWt Γ v A
local notation:40 Γ:41 "⊢ₐ" n:41 "∶" B:41 => ComWt Γ n B
local notation:40 Γ:41 "⊢ₐ" m:41 "∶" B:41 => CfgWt Γ m B

mutual
inductive ValWt : Ctxt → Val → ValType → Prop where
  | var {Γ x A} :
    Γ ∋ x ∶ A →
    -------------
    Γ ⊢ₐ var x ∶ A
  | unit {Γ} : Γ ⊢ₐ unit ∶ Unit
  | inl {Γ v} {A₁ A₂ : ValType} :
    Γ ⊢ₐ v ∶ A₁ →
    ---------------------
    Γ ⊢ₐ inl v ∶ Sum A₁ A₂
  | inr {Γ v} {A₁ A₂ : ValType} :
    Γ ⊢ₐ v ∶ A₂ →
    ---------------------
    Γ ⊢ₐ inr v ∶ Sum A₁ A₂
  | thunk {Γ B} {m : Cfg} :
    Γ ⊢ₐ m ∶ B →
    -----------------
    Γ ⊢ₐ thunk m ∶ U B

inductive ComWt : Ctxt → Com → ComType → Prop where
  | force {Γ v B} :
    Γ ⊢ₐ v ∶ U B →
    ---------------
    Γ ⊢ₐ force v ∶ B
  | lam {Γ A B} {m : Cfg} :
    Γ ∷ A ⊢ₐ m ∶ B →
    -------------------
    Γ ⊢ₐ lam m ∶ Arr A B
  | app {Γ v A B} {n : Com} :
    Γ ⊢ₐ n ∶ Arr A B →
    Γ ⊢ₐ v ∶ A →
    ---------------
    Γ ⊢ₐ app n v ∶ B
  | ret {Γ v} {A : ValType} :
    Γ ⊢ₐ v ∶ A →
    ---------------
    Γ ⊢ₐ ret v ∶ F A
  | prod {Γ B₁ B₂} {m₁ m₂ : Cfg} :
    Γ ⊢ₐ m₁ ∶ B₁ →
    Γ ⊢ₐ m₂ ∶ B₂ →
    ---------------------------
    Γ ⊢ₐ prod m₁ m₂ ∶ Prod B₁ B₂
  | fst {Γ B₁ B₂} {n : Com} :
    Γ ⊢ₐ n ∶ Prod B₁ B₂ →
    ---------------
    Γ ⊢ₐ fst n ∶ B₁
  | snd {Γ B₁ B₂} {n : Com} :
    Γ ⊢ₐ n ∶ Prod B₁ B₂ →
    ---------------
    Γ ⊢ₐ snd n ∶ B₂

inductive CfgWt : Ctxt → Cfg → ComType → Prop where
  | com {Γ B} {n : Com} :
    Γ ⊢ₐ n ∶ B →
    -------------
    Γ ⊢ₐ com n ∶ B
  | letin {Γ A B} {n : Com} {m : Cfg} :
    Γ ⊢ₐ n ∶ F A →
    Γ ∷ A ⊢ₐ m ∶ B →
    -----------------
    Γ ⊢ₐ letin n m ∶ B
  | case {Γ v A₁ A₂ B} {m₁ m₂ : Cfg} :
    Γ ⊢ₐ v ∶ Sum A₁ A₂ →
    Γ ∷ A₁ ⊢ₐ m₁ ∶ B →
    Γ ∷ A₂ ⊢ₐ m₂ ∶ B →
    --------------------
    Γ ⊢ₐ case v m₁ m₂ ∶ B
end
end

notation:40 Γ:41 "⊢ₐ" v:41 "∶" A:41 => ValWt Γ v A
notation:40 Γ:41 "⊢ₐ" n:41 "∶" B:41 => ComWt Γ n B
notation:40 Γ:41 "⊢ₐ" m:41 "∶" B:41 => CfgWt Γ m B

/-* Renaming and weakening lemmas *-/

theorem wtRenameA {ξ} {Γ Δ : Ctxt} (hξ : Δ ⊢ ξ ∶ Γ) :
  (∀ {v : ANF.Val} {A}, Γ ⊢ₐ v ∶ A → Δ ⊢ₐ ANF.renameVal ξ v ∶ A) ∧
  (∀ {m : ANF.Com} {B}, Γ ⊢ₐ m ∶ B → Δ ⊢ₐ ANF.renameCom ξ m ∶ B) ∧
  (∀ {m : ANF.Cfg} {B}, Γ ⊢ₐ m ∶ B → Δ ⊢ₐ ANF.renameCfg ξ m ∶ B) := by
  refine ⟨λ h ↦ ?wtv, λ h ↦ ?wtn, λ h ↦ ?wtm⟩
  mutual_induction h, h, h generalizing ξ Δ
  all_goals constructor
  all_goals apply_rules [wRenameLift]

theorem wtRenameVal {ξ} {Γ Δ : Ctxt} {v : ANF.Val} {A} :
  Δ ⊢ ξ ∶ Γ → Γ ⊢ₐ v ∶ A → Δ ⊢ₐ ANF.renameVal ξ v ∶ A :=
  λ hξ ↦ (wtRenameA hξ).left

theorem wtRenameCfg {ξ} {Γ Δ : Ctxt} {m : ANF.Cfg} {B} :
  Δ ⊢ ξ ∶ Γ → Γ ⊢ₐ m ∶ B → Δ ⊢ₐ ANF.renameCfg ξ m ∶ B :=
  λ hξ ↦ (wtRenameA hξ).right.right

/-* The translation continuation and plugging into a continuation *-/

inductive K : Type where
  | nil : K
  | app : ANF.Val → K → K
  | letin : ANF.Cfg → K
  | fst : K → K
  | snd : K → K

@[simp]
def plug (n : ANF.Com) : K → ANF.Cfg
  | .nil => .com n
  | .app v k => plug (.app n v) k
  | .letin m => .letin n m
  | .fst k => plug (.fst n) k
  | .snd k => plug (.snd n) k
notation:40 k:41 "[" n:41 "]" => plug n k

/-* Renaming continuations *-/

@[simp]
def renameK (ξ : Nat → Nat) : K → K
  | .nil => .nil
  | .app v k => .app (ANF.renameVal ξ v) (renameK ξ k)
  | .letin m => .letin (ANF.renameCfg (lift ξ) m)
  | .fst k => .fst (renameK ξ k)
  | .snd k => .snd (renameK ξ k)

theorem renameKExt {ξ ζ k} (h : ∀ x, ξ x = ζ x) : renameK ξ k = renameK ζ k := by
  induction k <;> simp [-lift]
  case app ih => exact ⟨ANF.renameValExt h, ih⟩
  case letin => exact ANF.renameCfgExt (liftExt ξ ζ h)
  case fst ih | snd ih => exact ih

theorem renameKComp {ξ ζ k} : (renameK ξ ∘ renameK ζ) k = renameK (ξ ∘ ζ) k := by
  induction k <;> simp [-lift]
  case app ih => exact ⟨ANF.renameValComp (λ _ ↦ rfl), ih⟩
  case letin => exact ANF.renameCfgComp (liftComp _ _ _ (λ _ ↦ rfl))
  case fst ih | snd ih => exact ih

theorem renameKLiftSucc {ξ k} : renameK succ (renameK ξ k) = renameK (lift ξ) (renameK succ k) := by
  calc renameK succ (renameK ξ k)
    _ = renameK (succ ∘ ξ) k              := renameKComp
    _ = renameK (lift ξ ∘ succ) k         := by rw [← renameKExt (liftSucc ξ)]
    _ = renameK (lift ξ) (renameK succ k) := Eq.symm renameKComp

theorem renamePlug {ξ n k} : ANF.renameCfg ξ (plug n k) = plug (ANF.renameCom ξ n) (renameK ξ k) := by
  induction k generalizing n <;> simp
  case app ih | fst ih | snd ih => simp [ih]

/-* Substitution continuations *-/

@[simp]
def substK (σ : Nat → Val) : K → K
  | .nil => .nil
  | .app v k => .app (substVal σ v) (substK σ k)
  | .letin m => .letin (substCfg (⇑ σ) m)
  | .fst k => .fst (substK σ k)
  | .snd k => .snd (substK σ k)

theorem substKId {k} : substK .var k = k := by
  induction k
  case nil => rfl
  case app ih => simp [substValId _, ih]
  case letin => simp [-up, substCfgExt (upId _ (λ _ ↦ rfl)), substCfgId]
  case fst ih | snd ih => simp [ih]

theorem substKExt {σ τ k} (h : ∀ x, σ x = τ x) : substK σ k = substK τ k := by
  induction k <;> simp [-lift]
  case app ih => exact ⟨ANF.substValExt h, ih⟩
  case letin => exact ANF.substCfgExt (upExt σ τ h)
  case fst ih | snd ih => exact ih

theorem substKComp {σ τ k} : (substK σ ∘ substK τ) k = substK (substVal σ ∘ τ) k := by
  induction k <;> simp [-lift, -up]
  case app ih => exact ⟨ANF.substValComp (λ _ ↦ rfl), ih⟩
  case letin => refine ANF.substCfgComp (upSubst _ _ _ (λ _ ↦ rfl))
  case fst ih | snd ih => exact ih

theorem substRenameK {ξ σ k} : substK σ (renameK ξ k) = substK (σ ∘ ξ) k := by
  induction k <;> simp [-lift, -up]
  case app ih => exact ⟨substRenameVal (λ _ ↦ rfl), ih⟩
  case letin => exact substRenameCfg (upLift _ _ _ (λ _ ↦ rfl))
  case fst ih | snd ih => exact ih

theorem renameSubstK {ξ σ k} : renameK ξ (substK σ k) = substK (renameVal ξ ∘ σ) k := by
  induction k <;> simp [-lift, -up]
  case app ih => exact ⟨renameSubstVal (λ _ ↦ rfl), ih⟩
  case letin => exact renameSubstCfg (upRename _ _ _ (λ _ ↦ rfl))
  case fst ih | snd ih => exact ih

theorem substKLiftSucc {σ k} : renameK succ (substK σ k) = substK (⇑ σ) (renameK succ k) := by
  calc renameK succ (substK σ k)
    _ = substK (renameVal succ ∘ σ) k := renameSubstK
    _ = substK (⇑ σ ∘ succ) k         := substKExt (upSucc σ)
    _ = substK (⇑ σ) (renameK succ k) := Eq.symm substRenameK

theorem substPlug {σ n k} : ANF.substCfg σ (plug n k) = plug (ANF.substCom σ n) (substK σ k) := by
  induction k generalizing n <;> simp
  case app ih | fst ih | snd ih => simp [ih]

/-* Typing continuations *-/

section
set_option hygiene false
open K
local notation:40 Γ:41 "⊢" k:41 "∶" B₁:41 "⇒" B₂:41 => KWt Γ k B₁ B₂
inductive KWt : Ctxt → K → ComType → ComType → Prop where
  | nil {Γ B} :
    ---------------
    Γ ⊢ nil ∶ B ⇒ B
  | app {Γ k v B₁ B₂} {A : ValType} :
    Γ ⊢ₐ v ∶ A →
    Γ ⊢ k ∶ B₁ ⇒ B₂ →
    -----------------------------
    Γ ⊢ app v k ∶ (Arr A B₁) ⇒ B₂
  | letin {Γ A} {m : ANF.Cfg} {B : ComType} :
    Γ ∷ A ⊢ₐ m ∶ B →
    ---------------------
    Γ ⊢ letin m ∶ F A ⇒ B
  | fst {Γ k B₁ B₂ B₃} :
    Γ ⊢ k ∶ B₁ ⇒ B₃ →
    -----------------------------
    Γ ⊢ fst k ∶ (Prod B₁ B₂) ⇒ B₃
  | snd {Γ k B₁ B₂ B₃} :
    Γ ⊢ k ∶ B₂ ⇒ B₃ →
    -----------------------------
    Γ ⊢ snd k ∶ (Prod B₁ B₂) ⇒ B₃
end
notation:40 Γ:41 "⊢" k:41 "∶" B₁:41 "⇒" B₂:41 => KWt Γ k B₁ B₂

/-* Renaming and weakening lemmas for continuations *-/

theorem wtRenameK {ξ} {Γ Δ : Ctxt} {k B₁ B₂}
  (hξ : Δ ⊢ ξ ∶ Γ) (h : Γ ⊢ k ∶ B₁ ⇒ B₂) : Δ ⊢ renameK ξ k ∶ B₁ ⇒ B₂ := by
  induction h <;> constructor
  all_goals apply_rules [wtRenameVal, wtRenameCfg, wRenameLift]

theorem wtWeakenK {Γ k A B₁ B₂} :
  Γ ⊢ k ∶ B₁ ⇒ B₂ → Γ ∷ A ⊢ renameK succ k ∶ B₁ ⇒ B₂ :=
  wtRenameK wRenameSucc

theorem wtPlug {Γ k B₁ B₂} {n : ANF.Com}
  (hk : Γ ⊢ k ∶ B₁ ⇒ B₂) (h : Γ ⊢ₐ n ∶ B₁) : Γ ⊢ₐ (k [ n ]) ∶ B₂ := by
  induction hk generalizing n
  case nil => exact .com h
  case app hv _ hn => exact hn (.app h hv)
  case letin hm => exact .letin h hm
  case fst hn => exact hn (.fst h)
  case snd hn => exact hn (.snd h)

/-* Composing continuations *-/

@[simp]
def compKCfg (k : K) : Cfg → Cfg
  | .com n => k [ n ]
  | .letin n m => .letin n (compKCfg (renameK succ k) m)
  | .case v m₁ m₂ => .case v (compKCfg (renameK succ k) m₁) (compKCfg (renameK succ k) m₂)

@[simp]
def compKK (k : K) : K → K
  | .nil => k
  | .app v k' => .app v (compKK k k')
  | .letin m => .letin (compKCfg (renameK succ k) m)
  | .fst k' => .fst (compKK k k')
  | .snd k' => .snd (compKK k k')

theorem compKCfgNil {m} : compKCfg .nil m = m := by
  mutual_induction m
  case com => rfl
  case letin ih => simp [ih]
  case case ih₁ ih₂ => simp [ih₁, ih₂]

theorem renameCompKCfg {ξ m k} : renameCfg ξ (compKCfg k m) = compKCfg (renameK ξ k) (renameCfg ξ m) := by
  mutual_induction m generalizing ξ k
  case com => simp [renamePlug]
  case letin ih => simp [ih, renameKLiftSucc]
  case case ihm₁ ihm₂ => simp [ihm₁, ihm₂, renameKLiftSucc]

theorem renameCompKK {ξ k₁ k₂} : renameK ξ (compKK k₁ k₂) = compKK (renameK ξ k₁) (renameK ξ k₂) := by
  induction k₂
  case nil => simp
  case app ih | fst ih | snd ih => simp [ih]
  case letin => simp [renameKLiftSucc, renameCompKCfg]

theorem compPlug {n k₁ k₂} : compKCfg k₁ (k₂ [ n ]) = ((compKK k₁ k₂) [ n ]) := by
  induction k₂ generalizing n <;> apply_assumption

end ANF

/-* A-normal translation of CBPV *-/

open Val Com

section
set_option hygiene false
local notation:1023 "⟦" v "⟧ᵥ" => Aval v
local notation:1023 "⟦" m "⟧ₘ" => Acom .nil m
local notation:1022 "⟦" m "⟧ₘ" k => Acom k m
mutual
@[simp]
def Aval : Val → ANF.Val
  | var x => .var x
  | unit => .unit
  | inl v => .inl ⟦ v ⟧ᵥ
  | inr v => .inr ⟦ v ⟧ᵥ
  | thunk m => .thunk ⟦ m ⟧ₘ

@[simp]
def Acom (k : ANF.K) : Com → ANF.Cfg
  | force v => k [ .force ⟦ v ⟧ᵥ ]
  | ret v   => k [ .ret ⟦ v ⟧ᵥ ]
  | lam m   => k [ .lam ⟦ m ⟧ₘ ]
  | app n v   => ⟦ n ⟧ₘ .app ⟦ v ⟧ᵥ k
  | letin n m => ⟦ n ⟧ₘ .letin (⟦ m ⟧ₘ ANF.renameK succ k)
  | case v m₁ m₂ => .case ⟦ v ⟧ᵥ (⟦ m₁ ⟧ₘ ANF.renameK succ k) (⟦ m₂ ⟧ₘ ANF.renameK succ k)
  | prod m₁ m₂ => k [ .prod ⟦ m₁ ⟧ₘ ⟦ m₂ ⟧ₘ ]
  | fst n => ⟦ n ⟧ₘ .fst k
  | snd n => ⟦ n ⟧ₘ .snd k
  /- I think this is the A-normalization with join points?
  | case v m₁ m₂ =>
    .letin (.ret (.thunk (.com (.lam ((renameK succ k) [ .force (.var 0) ])))))
      (.case (⟦ v ⟧ᵥ)
        (.com (.app (.force (.var 1)) (.thunk (ANF.renameCfg (lift succ) (⟦ m₁ ⟧ₘ)))))
        (.com (.app (.force (.var 1)) (.thunk (ANF.renameCfg (lift succ) (⟦ m₂ ⟧ₘ))))))
  -/
end
end
notation:1023 "⟦" v "⟧ᵥ" => Aval v
notation:1023 "⟦" m "⟧ₘ" => Acom ANF.K.nil m
notation:1022 "⟦" m "⟧ₘ" k => Acom k m

@[reducible, simp] def Asubst (σ : Nat → Val) : Nat → ANF.Val := λ x ↦ ⟦ σ x ⟧ᵥ
notation:1023 "⟦" σ "⟧ₛ" => Asubst σ

/-* Translation is type preserving *-/

theorem preservation {Γ} :
  (∀ {v} {A : ValType}, Γ ⊢ v ∶ A → Γ ⊢ₐ ⟦ v ⟧ᵥ ∶ A) ∧
  (∀ {k m} {B₁ B₂ : ComType}, Γ ⊢ k ∶ B₁ ⇒ B₂ → Γ ⊢ m ∶ B₁ → Γ ⊢ₐ ⟦ m ⟧ₘ k ∶ B₂) := by
  refine ⟨λ h ↦ ?val, λ hk h ↦ ?com⟩
  mutual_induction h, h
  case var mem => exact .var mem
  case unit => exact .unit
  case inl h => exact .inl h
  case inr h => exact .inr h
  case thunk h => exact .thunk (h .nil)
  case force h _ _ => exact (ANF.wtPlug hk (.force h))
  case ret h _ _ => exact (ANF.wtPlug hk (.ret h))
  case lam h _ _ => exact (ANF.wtPlug hk (.lam (h .nil)))
  case app hn hv k _ => exact hn (.app hv hk)
  case letin hn hm _ _ => exact hn (.letin (hm (ANF.wtWeakenK hk)))
  case case hv hm₁ hm₂ _ _ => exact .case hv (hm₁ (ANF.wtWeakenK hk)) (hm₂ (ANF.wtWeakenK hk))
  case prod hm₁ hm₂ _ _ => exact ANF.wtPlug hk (.prod (hm₁ .nil) (hm₂ .nil))
  case fst h _ _ => exact h (.fst hk)
  case snd h _ _ => exact h (.snd hk)

/-* Renaming commutes with translation *-/

theorem renameA {ξ} :
  (∀ v, ⟦ renameVal ξ v ⟧ᵥ = ANF.renameVal ξ ⟦ v ⟧ᵥ) ∧
  (∀ m k, (⟦ renameCom ξ m ⟧ₘ ANF.renameK ξ k) = ANF.renameCfg ξ (⟦ m ⟧ₘ k)) := by
  refine ⟨λ v ↦ ?val, λ m k ↦ ?com⟩
  mutual_induction v, m generalizing ξ
  case var | unit => rfl
  case inl ih | inr ih => simp [ih]
  case thunk ih => simp; exact ih .nil
  case force ih | ret ih => simp [ih, ANF.renamePlug]
  case lam ih =>
    have e := ih (ξ := lift ξ) .nil
    simp [-lift] at *; rw [e]; simp [ANF.renamePlug]
  case app ihm ihv => simp [-lift, ihv, ← ihm]
  case letin ihn ihm =>
    simp [-lift, ← ihn, ← ihm, ANF.renameKLiftSucc]
  case case ihv ihm₁ ihm₂ =>
    simp [-lift, ihv, ← ihm₁, ← ihm₂, ANF.renameKLiftSucc]
  case prod ihm₁ ihm₂ => simp [← ihm₁, ← ihm₂, ANF.renamePlug]
  case fst ih | snd ih => simp [← ih]

theorem renameAval {ξ v} : ⟦ renameVal ξ v ⟧ᵥ = ANF.renameVal ξ ⟦ v ⟧ᵥ := renameA.left v
theorem renameAcom {ξ m k} : (⟦ renameCom ξ m ⟧ₘ ANF.renameK ξ k) = ANF.renameCfg ξ (⟦ m ⟧ₘ k) := renameA.right m k

/-* Substitution commutes with translation *-/

theorem substAupCfg {σ m} : ANF.substCfg ⟦ ⇑ σ ⟧ₛ m = ANF.substCfg (⇑ ⟦ σ ⟧ₛ) m := by
  apply ANF.substCfgExt; intro n; cases n <;> simp [renameAval]

theorem substAupK {σ k} : ANF.substK ⟦ ⇑ σ ⟧ₛ k = ANF.substK (⇑ ⟦ σ ⟧ₛ) k := by
  apply ANF.substKExt; intro n; cases n <;> simp [renameAval]

theorem substA {σ} :
  (∀ v, ⟦ substVal σ v ⟧ᵥ = ANF.substVal ⟦ σ ⟧ₛ ⟦ v ⟧ᵥ) ∧
  (∀ m k, (⟦ substCom σ m ⟧ₘ ANF.substK ⟦ σ ⟧ₛ k) = ANF.substCfg ⟦ σ ⟧ₛ (⟦ m ⟧ₘ k)) := by
  refine ⟨λ v ↦ ?val, λ m k ↦ ?com⟩
  mutual_induction v, m generalizing σ
  case var | unit => rfl
  case inl ih | inr ih => simp [ih]
  case thunk ih => simp; exact ih .nil
  case force ih | ret ih => simp [ih, ANF.substPlug]
  case lam ih =>
    have e := ih (σ := ⇑ σ) .nil
    simp [-lift, -up] at *; rw [e]; simp [-up, ANF.substPlug, substAupCfg]
  case app ihm ihv => simp [-up, ← ihv, ← ihm]
  case letin ihn ihm =>
    simp [-lift, -up, -ANF.up, ← ihn, ← substAupCfg, ← ihm, ANF.substKLiftSucc, substAupK]
  case case ihv ihm₁ ihm₂ =>
    have eσ {σ} : (.var 0 +: ANF.renameVal succ ∘ σ) = ⇑ σ := rfl
    simp [-lift, -up, -ANF.up, ihv, ANF.substKLiftSucc, ← substAupCfg, ← substAupK, ihm₁, ihm₂]
  case prod ihm₁ ihm₂ => simp [← ihm₁, ← ihm₂, ANF.substPlug]
  case fst ih | snd ih => simp [← ih]

theorem substAval {σ v} : ⟦ substVal σ v ⟧ᵥ = ANF.substVal ⟦ σ ⟧ₛ ⟦ v ⟧ᵥ := substA.left v
theorem substAcom {σ m k} : (⟦ substCom σ m ⟧ₘ ANF.substK ⟦ σ ⟧ₛ k) = ANF.substCfg ⟦ σ ⟧ₛ (⟦ m ⟧ₘ k) := substA.right m k

theorem substAcomOne {m : Com} {v : Val} {k} : ANF.substCfg (⟦ v ⟧ᵥ +: .var) (⟦ m ⟧ₘ ANF.renameK succ k) = (⟦ m⦃v⦄ ⟧ₘ k) := by
  calc ANF.substCfg (⟦ v ⟧ᵥ +: .var) (⟦ m ⟧ₘ ANF.renameK succ k)
    _ = ANF.substCfg (⟦ v +: .var ⟧ₛ) (⟦ m ⟧ₘ ANF.renameK succ k)  := by rw [ANF.substCfgExt (λ n ↦ ?_)]; cases n <;> simp
    _ = ⟦ m⦃v⦄ ⟧ₘ (ANF.substK ⟦ v +: .var ⟧ₛ (ANF.renameK succ k)) := Eq.symm substAcom
    _ = ⟦ m⦃v⦄ ⟧ₘ (ANF.substK (⟦ v +: .var ⟧ₛ ∘ succ) k)           := by rw [ANF.substRenameK]
    _ = ⟦ m⦃v⦄ ⟧ₘ (ANF.substK .var k)                              := by rw [ANF.substKExt (λ n ↦ ?_)]; cases n <;> simp
    _ = ⟦ m⦃v⦄ ⟧ₘ k                                                := by rw [ANF.substKId]

/-* Continuation composition commutes with translation *-/

theorem compA {m k₁ k₂} : ANF.compKCfg k₁ (⟦ m ⟧ₘ k₂) = ⟦ m ⟧ₘ ANF.compKK k₁ k₂ := by
  mutual_induction m generalizing k₁ k₂
  case force | lam | ret => exact ANF.compPlug
  case app ih | fst ih | snd ih => simp [ih]
  case letin ihn ihm => simp [ihn, ihm, ANF.renameCompKK]
  case case ihm₁ ihm₂ => simp [ihm₁, ihm₂, ANF.renameCompKK]
  case prod ihm₁ ihm₂ => simp [ihm₁, ihm₂, ANF.compPlug]

/-* CK machine semantics of ANF *-/

namespace ANF

inductive F : Type where
  | app : Val → F
  | letin : Cfg → F
  | fst : F
  | snd : F
open F

@[reducible] def Sₐ := List F
@[reducible] def CK := Cfg × Sₐ

@[simp]
def renameKₐ (ξ : Nat → Nat) : Sₐ → Sₐ
  | [] => []
  | .app v :: k => .app (renameVal ξ v) :: renameKₐ ξ k
  | .letin m :: k => .letin (renameCfg (lift ξ) m) :: renameKₐ ξ k
  | .fst :: k => fst :: renameKₐ ξ k
  | .snd :: k => snd :: renameKₐ ξ k

section
set_option hygiene false
local infix:40 "⤳" => Step
inductive Step : CK → CK → Prop where
  | π {m k} :        ⟨.com (.force (.thunk m)), k⟩   ⤳ ⟨m, k⟩
  | β {m v k} :      ⟨.com (.lam m), .app v :: k⟩    ⤳ ⟨substCfg (v +: .var) m, k⟩
  | ζ {v m k} :      ⟨.com (.ret v), .letin m :: k⟩  ⤳ ⟨substCfg (v +: .var) m, k⟩
  | ιl {v m₁ m₂ k} : ⟨.case (.inl v) m₁ m₂, k⟩       ⤳ ⟨substCfg (v +: .var) m₁, k⟩
  | ιr {v m₁ m₂ k} : ⟨.case (.inr v) m₁ m₂, k⟩       ⤳ ⟨substCfg (v +: .var) m₂, k⟩
  | π1 {m₁ m₂ k} :   ⟨.com (.prod m₁ m₂), .fst :: k⟩ ⤳ ⟨m₁, k⟩
  | π2 {m₁ m₂ k} :   ⟨.com (.prod m₁ m₂), .snd :: k⟩ ⤳ ⟨m₂, k⟩
  | app {n v k} :    ⟨.com (.app n v), k⟩            ⤳ ⟨.com n, .app v :: k⟩
  | letin {n m k} :  ⟨.letin n m, k⟩                 ⤳ ⟨.com n, .letin m :: k⟩
  | fst {n k} :      ⟨.com (.fst n), k⟩              ⤳ ⟨.com n, .fst :: k⟩
  | snd {n k} :      ⟨.com (.snd n), k⟩              ⤳ ⟨.com n, .snd :: k⟩
end
infix:40 "⤳" => Step

@[reducible] def Steps := RTC Step
infix:40 "⤳⋆"  => Steps

end ANF

/-* Translating stacks and continuations *-/

@[simp]
def SK : S → ANF.K
  | [] => .nil
  | .app v :: k => .app ⟦ v ⟧ᵥ (SK k)
  | .letin m :: k => .letin (⟦ m ⟧ₘ ANF.renameK succ (SK k))
  | .fst :: k => .fst (SK k)
  | .snd :: k => .snd (SK k)

@[simp]
def SSₐ : S → ANF.Sₐ
  | [] => []
  | .app v :: k => .app ⟦ v ⟧ᵥ :: SSₐ k
  | .letin m :: k => .letin ⟦ m ⟧ₘ :: SSₐ k
  | .fst :: k => .fst :: SSₐ k
  | .snd :: k => .snd :: SSₐ k
notation:1023 "⟦" k:41 "⟧ₛₛ" => SSₐ k

theorem renameSK {k} (ξ : Nat → Nat) : SK (renameS ξ k) = ANF.renameK ξ (SK k) := by
  induction k
  case nil => simp
  case cons f _ ih =>
    cases f <;> simp [-lift, ih, renameAval, ← renameAcom, ← ANF.renameKLiftSucc]

theorem renameSSₐ {k} (ξ : Nat → Nat) : ⟦ renameS ξ k ⟧ₛₛ = ANF.renameKₐ ξ ⟦ k ⟧ₛₛ := by
  induction k
  case nil => simp
  case cons f _ ih =>
    cases f <;> simp [-lift, ih, renameAval, ← renameAcom, ← ANF.renameKLiftSucc, renameSK]

/-* Translation preserves machine semantics *-/

theorem loopK₁ {f : CK.F} {k : S} (e : f :: k = k) : False := by
  induction k generalizing f
  case nil => injection e
  case cons ih => injection e with _ e; exact ih e

theorem loopK₂ {f₁ f₂ : CK.F} {k : S} (e : f₁ :: f₂ :: k = k) : False := by
  induction k generalizing f₁ f₂
  case nil => injection e
  case cons ih => injection e with _ e; exact ih e

theorem CKeqv₁ {m₁ m₂ f} {k : S} (r : ⟨m₁, f :: k⟩ ⤳ ⟨m₂, k⟩) : ⟨⟦ m₁ ⟧ₘ, ⟦ f :: k ⟧ₛₛ⟩ ⤳ ⟨⟦ m₂ ⟧ₘ, ⟦ k ⟧ₛₛ⟩ := by
  generalize e : f :: k = k' at r
  cases r
  all_goals try cases loopK₁ e
  all_goals try cases loopK₂ e
  all_goals injection e with ef ek; subst ef; clear ek
  case β m v =>
    calc ⟨.com (.lam ⟦ m ⟧ₘ), .app ⟦ v ⟧ᵥ :: ⟦ k ⟧ₛₛ⟩
      _ ⤳ ⟨ANF.substCfg (⟦ v ⟧ᵥ +: .var) ⟦ m ⟧ₘ, ⟦ k ⟧ₛₛ⟩ := .β
      _ = ⟨ANF.substCfg ⟦ v +: .var ⟧ₛ ⟦ m ⟧ₘ, ⟦ k ⟧ₛₛ⟩    := by rw [ANF.substCfgExt (λ n ↦ ?_)]; cases n <;> rfl
      _ = ⟨⟦ m⦃v⦄ ⟧ₘ, ⟦ k ⟧ₛₛ⟩                             := by rw [← substAcom]; rfl
  case ζ v m =>
    calc ⟨.com (.ret ⟦ v ⟧ᵥ), .letin ⟦ m ⟧ₘ :: ⟦ k ⟧ₛₛ⟩
      _ ⤳ ⟨ANF.substCfg (⟦ v ⟧ᵥ +: .var) ⟦ m ⟧ₘ, ⟦ k ⟧ₛₛ⟩ := .ζ
      _ = ⟨ANF.substCfg ⟦ v +: .var ⟧ₛ ⟦ m ⟧ₘ, ⟦ k ⟧ₛₛ⟩    := by rw [ANF.substCfgExt (λ n ↦ ?_)]; cases n <;> rfl
      _ = ⟨⟦ m⦃v⦄ ⟧ₘ .nil, ⟦ k ⟧ₛₛ⟩                        := by rw [← substAcom]; rfl
  case π1 | π2 => constructor

theorem CKeqv₂ {m₁ m₂} {k : S} (r : ⟨m₁, k⟩ ⤳ ⟨m₂, k⟩) : ⟨⟦ m₁ ⟧ₘ, ⟦ k ⟧ₛₛ⟩ ⤳ ⟨⟦ m₂ ⟧ₘ, ⟦ k ⟧ₛₛ⟩ := by
  generalize e : (m₂, k) = ck₂ at r
  cases r
  all_goals injection e with em ek; subst em
  all_goals try cases loopK₁ ek
  all_goals try cases loopK₁ (Eq.symm ek)
  case π => constructor
  case ιl v m₁ m₂ =>
    calc ⟨.case (.inl ⟦ v ⟧ᵥ) ⟦ m₁ ⟧ₘ ⟦ m₂ ⟧ₘ, ⟦ k ⟧ₛₛ⟩
      _ ⤳ ⟨ANF.substCfg (⟦ v ⟧ᵥ +: .var) ⟦ m₁ ⟧ₘ, ⟦ k ⟧ₛₛ⟩ := .ιl
      _ = ⟨ANF.substCfg ⟦ v +: .var ⟧ₛ ⟦ m₁ ⟧ₘ, ⟦ k ⟧ₛₛ⟩    := by rw [ANF.substCfgExt (λ n ↦ ?_)]; cases n <;> rfl
      _ = ⟨⟦ m₁⦃v⦄ ⟧ₘ, ⟦ k ⟧ₛₛ⟩                             := by rw [← substAcom]; rfl
  case ιr v m₁ m₂ =>
    calc ⟨.case (.inr ⟦ v ⟧ᵥ) ⟦ m₁ ⟧ₘ ⟦ m₂ ⟧ₘ, ⟦ k ⟧ₛₛ⟩
      _ ⤳ ⟨ANF.substCfg (⟦ v ⟧ᵥ +: .var) ⟦ m₂ ⟧ₘ, ⟦ k ⟧ₛₛ⟩ := .ιr
      _ = ⟨ANF.substCfg ⟦ v +: .var ⟧ₛ ⟦ m₂ ⟧ₘ, ⟦ k ⟧ₛₛ⟩    := by rw [ANF.substCfgExt (λ n ↦ ?_)]; cases n <;> rfl
      _ = ⟨⟦ m₂⦃v⦄ ⟧ₘ, ⟦ k ⟧ₛₛ⟩                             := by rw [← substAcom]; rfl

theorem CKeqv₃ {m₁ m₂ f} {k : S} (r : ⟨m₁, k⟩ ⤳ ⟨m₂, f :: k⟩) : (⟦ m₁ ⟧ₘ SK k) = (⟦ m₂ ⟧ₘ SK (f :: k)) := by
  generalize e : f :: k = k' at r
  cases r
  all_goals try cases loopK₁ e
  all_goals try cases loopK₂ e
  all_goals rfl

/-* Equational theory of ANF *-/

namespace ANF
section
set_option hygiene false
local infix:40 "≡ᵥ" => EqVal
local infix:40 "≡ₙ" => EqCom
local infix:40 "≡ₘ" => EqCfg
mutual
inductive EqVal : Val → Val → Prop
  | var {x} : .var x ≡ᵥ .var x
  | unit : .unit ≡ᵥ .unit
  | inl {v w} : v ≡ᵥ w → .inl v ≡ᵥ .inl w
  | inr {v w} : v ≡ᵥ w → .inr v ≡ᵥ .inr w
  | thunk {m n} : m ≡ₘ n → .thunk m ≡ᵥ .thunk n
  | sym {v w} : w ≡ᵥ v → v ≡ᵥ w
  | trans {u v w} : u ≡ᵥ v → v ≡ᵥ w → u ≡ᵥ w

inductive EqCom : Com → Com → Prop
  | force {v w} : v ≡ᵥ w → .force v ≡ₙ .force w
  | lam {m n} : m ≡ₘ n → .lam m ≡ₙ .lam n
  | app {m n v w} : m ≡ₙ n → v ≡ᵥ w → .app m v ≡ₙ .app n w
  | ret {v w} : v ≡ᵥ w → .ret v ≡ₙ .ret w
  | prod {m₁ m₂ n₁ n₂} : m₁ ≡ₘ n₁ → m₂ ≡ₘ n₂ → .prod m₁ m₂ ≡ₙ .prod n₁ n₂
  | fst {m n} : m ≡ₙ n → .fst m ≡ₙ .fst n
  | snd {m n} : m ≡ₙ n → .snd m ≡ₙ .snd n
  | sym {m n} : n ≡ₙ m → m ≡ₙ n
  | trans {m n p} : m ≡ₙ n → n ≡ₙ p → m ≡ₙ p

inductive EqCfg : Cfg → Cfg → Prop
  | com {m n} : m ≡ₙ n → .com m ≡ₘ .com n
  | letin {m₁ m₂ n₁ n₂} : m₁ ≡ₙ n₁ → m₂ ≡ₘ n₂ → .letin m₁ m₂ ≡ₘ .letin n₁ n₂
  | case {v w m₁ n₁ m₂ n₂} : v ≡ᵥ w → m₁ ≡ₘ n₁ → m₂ ≡ₘ n₂ → .case v m₁ m₂ ≡ₘ .case w n₁ n₂
  | β {m v} : .com (.app (.lam m) v) ≡ₘ substCfg (v +: .var) m
  | π {m} : .com (.force (.thunk m)) ≡ₘ m
  | π1 {m₁ m₂} : .com (.fst (.prod m₁ m₂)) ≡ₘ m₁
  | π2 {m₁ m₂} : .com (.snd (.prod m₁ m₂)) ≡ₘ m₂
  | ζ {m v} : .letin (.ret v) m ≡ₘ substCfg (v +: .var) m
  | ιl {v m₁ m₂} : .case (.inl v) m₁ m₂ ≡ₘ substCfg (v +: .var) m₁
  | ιr {v m₁ m₂} : .case (.inr v) m₁ m₂ ≡ₘ substCfg (v +: .var) m₂
  | sym {m n} : n ≡ₘ m → m ≡ₘ n
  | trans {m n p} : m ≡ₘ n → n ≡ₘ p → m ≡ₘ p
end
end
infix:40 "≡ᵥ" => EqVal
infix:40 "≡ₙ" => EqCom
infix:40 "≡ₘ" => EqCfg

theorem reflValCom :
  (∀ {v : Val}, v ≡ᵥ v) ∧
  (∀ {n : Com}, n ≡ₙ n) ∧
  (∀ {m : Cfg}, m ≡ₘ m) := by
  refine ⟨λ {v} ↦ ?val, λ {n} ↦ ?com, λ {m} ↦ ?cfg⟩
  mutual_induction v, n, m
  all_goals constructor <;> assumption

@[refl] theorem EqVal.refl : ∀ {v : Val}, v ≡ᵥ v := reflValCom.left
@[refl] theorem EqCom.refl : ∀ {n : Com}, n ≡ₙ n := reflValCom.right.left
@[refl] theorem EqCfg.refl : ∀ {m : Cfg}, m ≡ₘ m := reflValCom.right.right

instance : Trans EqVal EqVal EqVal where
  trans := .trans

instance : Trans EqCom EqCom EqCom where
  trans := .trans

instance : Trans EqCfg EqCfg EqCfg where
  trans := .trans

theorem EqCom.plug {n₁ n₂ k} (e : n₁ ≡ₙ n₂) : (k [ n₁ ]) ≡ₘ (k [ n₂ ]) := by
  induction k generalizing n₁ n₂
  case' app ih | fst ih | snd ih => apply ih
  all_goals constructor; assumption; try rfl

theorem EqCom.compK {n m k} (e : .com n ≡ₘ m) : (k [ n ]) ≡ₘ compKCfg k m := by
  mutual_induction m generalizing n k
  case com => apply EqCom.plug; sorry
  case letin => simp; sorry
  case case ihm₁ ihm₂ => simp; sorry

end ANF

theorem waaaahEq :
  (∀ {v w : Val}, v ≡ w → ⟦ v ⟧ᵥ ≡ᵥ ⟦ w ⟧ᵥ) ∧
  (∀ {k} {m n : Com}, m ≡ n → (⟦ m ⟧ₘ k) ≡ₘ (⟦ n ⟧ₘ k)) := by
  refine ⟨λ ev ↦ ?eqval, λ em ↦ ?eqcom⟩
  mutual_induction ev, em
  case var | unit | inl ih | inr ih | thunk ih =>
    constructor; try simp [ih]
  case force | lam | ret | prod =>
    apply ANF.EqCom.plug; constructor <;> apply_assumption
  case case ihv ihm₁ ihm₂ _ => constructor <;> apply_assumption
  case app ihm ihv _ | letin ihn ihm _ => simp; sorry -- equality of continuations
  case fst ih _ | snd ih _ => exact ih
  case eqval.sym e => exact .sym e
  case eqval.trans e₁ e₂ => exact .trans e₁ e₂
  case eqcom.sym e _ => exact .sym e
  case eqcom.trans e₁ e₂ _ => exact .trans e₁ e₂
  case β k =>
    have eknil (k : ANF.K) : k = ANF.compKK k .nil := by rfl
    rw [eknil k, ← compA, ← compA]; simp
    apply ANF.EqCom.compK
    rw [← substAcomOne]; simp
    constructor
  case ζ k => rw [← substAcomOne]; constructor
  case π k | π1 k | π2 k =>
    have eknil (k : ANF.K) : k = ANF.compKK k .nil := by rfl
    simp; rw [eknil k, ← compA]
    apply ANF.EqCom.compK
    constructor
  case ιl v m₁ m₂ k => rw [← substAcomOne]; exact .ιl
  case ιr v m₁ m₂ k => rw [← substAcomOne]; exact .ιr

/-* Big step semantics of ANF *-/

namespace ANF

section
set_option hygiene false
local infix:40 "⇓" => StepCom
local infix:40 "⇓" => StepCfg
mutual
inductive StepCom : Com → Com → Prop where
  | lam {m : Cfg} : .lam m ⇓ .lam m
  | ret {v : Val} : .ret v ⇓ .ret v
  | prod {m₁ m₂ : Cfg} : .prod m₁ m₂ ⇓ .prod m₁ m₂
  | π {m : Cfg} {t} :
    m ⇓ t →
    ---------------------
    .force (.thunk m) ⇓ t
  | β {n t : Com} {m v} :
    n ⇓ .lam m →
    substCfg (v +: .var) m ⇓ t →
    -----------------------------
    .app n v ⇓ t
  | π1 {n t : Com} {m₁ m₂} :
    n ⇓ .prod m₁ m₂ →
    m₁ ⇓ t →
    -----------
    .fst n ⇓ t
  | π2 {n t : Com} {m₁ m₂} :
    n ⇓ .prod m₁ m₂ →
    m₂ ⇓ t →
    -----------
    .snd n ⇓ t

inductive StepCfg : Cfg → Com → Prop where
  | com {n t : Com} : n ⇓ t → .com n ⇓ t
  | ζ {n t : Com} {v m} :
    n ⇓ .ret v →
    substCfg (v +: .var) m ⇓ t →
    -----------------------------
    .letin n m ⇓ t
  | ιl {v m₁ m₂ t}:
    substCfg (v +: .var) m₁ ⇓ t →
    -----------------------------
    .case (.inl v) m₁ m₂ ⇓ t
  | ιr {v m₁ m₂ t}:
    substCfg (v +: .var) m₂ ⇓ t →
    -----------------------------
    .case (.inr v) m₁ m₂ ⇓ t
end
end
infix:40 "⇓" => StepCom
infix:40 "⇓" => StepCfg

@[simp]
def isTerminal : Com → Prop
  | .lam _ | .ret _ | .prod _ _ => True
  | _ => False

theorem stepTerminal {t} :
  (∀ {n : Com}, n ⇓ t → isTerminal t) ∧
  (∀ {m : Cfg}, m ⇓ t → isTerminal t) := by
  refine ⟨λ {n} r ↦ ?com, λ {m} r ↦ ?cfg⟩
  mutual_induction r, r
  case lam | ret | prod => constructor
  all_goals assumption

theorem StepCfg.compK {m : Cfg} {n t : Com} {k} (h : ∀ t, m ⇓ t → n ⇓ t) (b : compKCfg k m ⇓ t) : (k [ n ]) ⇓ t := by
  mutual_induction n generalizing m t
  case app => sorry
  all_goals sorry
end ANF

theorem waaahBig {m₁ m₂ : Com} {k₁ k₂ t} (r : ⟨m₁, k₁⟩ ⤳ ⟨m₂, k₂⟩) (b : (⟦ m₂ ⟧ₘ SK k₂) ⇓ t) : (⟦ m₁ ⟧ₘ SK k₁) ⇓ t := by
  generalize e₁ : (m₁, k₁) = ck₁ at r
  generalize e₂ : (m₂, k₂) = ck₂ at r
  induction r
  all_goals injection e₁ with em ek; subst em ek
  all_goals injection e₂ with em ek; subst em ek
  case β => simp; sorry
  all_goals sorry

/-* Failed proofs *-/

@[simp]
def SₐK : ANF.Sₐ → ANF.K
  | [] => .nil
  | .app v :: k => .app v (SₐK k)
  | .letin m :: k => .letin (ANF.compKCfg (SₐK k) m)
  | .fst :: k => .fst (SₐK k)
  | .snd :: k => .snd (SₐK k)

theorem CKeqv' {m₁ m₂} {k₁ : S} (r : ⟨m₁, k₁⟩ ⤳⋆ ⟨m₂, []⟩) : ∃ m k, ⟨m, k⟩ ⤳⋆ ⟨⟦ m₂ ⟧ₘ, []⟩ ∧ (⟦ m₁ ⟧ₘ SK k₁) = (ANF.compKCfg (SₐK k) m) := by
  generalize e₁ : (m₁, k₁) = ck₁ at r
  generalize e₂ : (m₂, []) = ck₂ at r
  induction r generalizing m₁ m₂ k₁
  case refl =>
    subst e₁; injection e₂ with em ek; subst em ek
    exists ⟦ m₂ ⟧ₘ, []; simp [ANF.compKCfgNil]; rfl
  case trans ck _ r _ ih =>
    subst e₁ e₂
    let ⟨m', k', r', e⟩ := ih rfl rfl
    cases r
    case β m v k r =>
      simp at *
      exists .com (.lam ⟦ m ⟧ₘ), .app ⟦ v ⟧ᵥ :: ⟦ k ⟧ₛₛ
      constructor
      apply RTC.trans' ?_ r'
      all_goals sorry
    all_goals sorry

theorem appendNil {α} {xs : List α} : xs = xs ++ [] := by
  induction xs <;> simp

theorem CKeqv'' {m₁ m₂ : Com} {k₁ k₂} (r : ⟨m₁, k₁⟩ ⤳ ⟨m₂, k₂⟩) :
  ∃ k₁₁ k₁₂ k₂₁ k₂₂,
    ⟨⟦ m₁ ⟧ₘ SK k₁₁, k₁₂⟩ ⤳⋆ ⟨⟦ m₂ ⟧ₘ SK k₂₁, k₂₂⟩ ∧
    ⟦ k₁ ⟧ₛₛ = ⟦ k₁₁ ⟧ₛₛ ++ k₁₂ ∧
    ⟦ k₂ ⟧ₛₛ = ⟦ k₂₁ ⟧ₛₛ ++ k₂₂ := by
  generalize e₁ : (m₁, k₁) = ck₁ at r
  generalize e₂ : (m₂, k₂) = ck₂ at r
  induction r
  all_goals injection e₁ with em ek; subst em ek
  all_goals injection e₂ with em ek; subst em ek
  case β m v =>
    exact ⟨.nil, ⟦ .app v :: k₂ ⟧ₛₛ, .nil, _, .once (CKeqv₁ .β), rfl, rfl⟩
  case app v =>
    refine ⟨_, .nil, .app v :: k₁ , .nil, by rw [CKeqv₃ .app], appendNil, appendNil⟩
  all_goals sorry

theorem CKeqv''' {m₁ m₂ : Com} {k₁ k₂} (r : ⟨m₁, k₁⟩ ⤳⋆ ⟨m₂, k₂⟩) :
  ∃ k₁₁ k₁₂ k₂₁ k₂₂,
    ⟨⟦ m₁ ⟧ₘ SK k₁₁, k₁₂⟩ ⤳⋆ ⟨⟦ m₂ ⟧ₘ SK k₂₁, k₂₂⟩ ∧
    ⟦ k₁ ⟧ₛₛ = ⟦ k₁₁ ⟧ₛₛ ++ k₁₂ ∧
    ⟦ k₂ ⟧ₛₛ = ⟦ k₂₁ ⟧ₛₛ ++ k₂₂ := by
  generalize e₁ : (m₁, k₁) = ck₁ at r
  generalize e₂ : (m₂, k₂) = ck₂ at r
  induction r generalizing m₁ k₁
  case refl =>
    subst e₁; injection e₂ with em ek; subst em ek
    exists k₂, .nil, k₂, .nil
    rw [← appendNil]; simp; rfl
  case trans ck _ r _ ih =>
    subst e₁ e₂
    match ck with
    | .mk m₂ k₂ =>
    match ih rfl rfl with
    | ⟨_, _, _, _, r₂, e₁, e₂⟩ =>
    refine ⟨?_, ?_, _, _, RTC.trans' ?_ r₂, ?_, e₂⟩
    all_goals sorry

theorem CKeqv'''' {m₁ m₂} {k : S} (r : ⟨m₁, k⟩ ⤳⋆ ⟨m₂, []⟩) :
  ∃ k₁ k₂, ⟨⟦ m₁ ⟧ₘ SK k₁, k₂⟩ ⤳⋆ ⟨⟦ m₂ ⟧ₘ, []⟩ ∧ (⟦ k ⟧ₛₛ) = (⟦ k₁ ⟧ₛₛ) ++ k₂ := by
  generalize e₁ : (m₁, k) = ck₁ at r
  generalize e₂ : (m₂, []) = ck₂ at r
  induction r generalizing m₁ k
  case refl =>
    subst e₁; injection e₂ with em ek; subst em ek
    exists .nil, []
  case trans ck₁ _ r _ ih =>
    subst e₁ e₂
    match ck₁ with
    | .mk m₂ k₂ => sorry

/-
@[simp]
def Asubst (σ : Nat → Val) : Nat → ANF.Val := λ x ↦ ⟦ σ x ⟧ᵥ
notation:40 "⟦" σ:41 "⟧ₛ" => Asubst σ

theorem Alookup {σ x} : (⟦ σ x ⟧ᵥ) = (⟦ σ ⟧ₛ) x := by
  cases x <;> simp

theorem Acons {σ v} : (⟦ v +: σ ⟧ₛ) = ((⟦ v ⟧ᵥ) +: (⟦ σ ⟧ₛ)) :=
  funext (λ x ↦ by cases x <;> simp)

def CEK := Com × (Nat → Val) × List F
def ACEK := ANF.Cfg × (Nat → ANF.Val) × List Fₐ

section
set_option hygiene false
local notation:40 cek:41 "⤳" cek':41 => eval cek cek'
inductive eval : CEK → CEK → Prop where
  | force {σ fs m}       : ⟨force (thunk m), σ, fs⟩    ⤳ ⟨m, σ, fs⟩
  | force' {σ fs x}      : ⟨force (var x), σ, fs⟩      ⤳ ⟨force (σ x), σ, fs⟩
  | lam {σ fs m v}       : ⟨lam m, σ, .app v :: fs⟩    ⤳ ⟨m, v +: σ, renameF succ fs⟩
  | app {σ fs m v}       : ⟨app m v, σ, fs⟩            ⤳ ⟨m, σ, .cons (.app v) fs⟩
  | ret {σ fs m v}       : ⟨ret v, σ, .letin m :: fs⟩  ⤳ ⟨m, v +: σ, renameF succ fs⟩
  | letin {σ fs n m}     : ⟨letin n m, σ, fs⟩          ⤳ ⟨n, σ, .cons (.letin m) fs⟩
  | case₁ {σ fs v m₁ m₂} : ⟨case (inl v) m₁ m₂, σ, fs⟩ ⤳ ⟨m₁, v +: σ, renameF succ fs⟩
  | case₂ {σ fs v m₁ m₂} : ⟨case (inr v) m₁ m₂, σ, fs⟩ ⤳ ⟨m₂, v +: σ, renameF succ fs⟩
  | case' {σ fs m₁ m₂ x} : ⟨case (var x) m₁ m₂, σ, fs⟩ ⤳ ⟨case (σ x) m₁ m₂, σ, fs⟩
end
notation:40 cek:41 "⤳" cek':41 => eval cek cek'

section
set_option hygiene false
local notation:40 acek:41 "⤳ₐ" acek':41 => aeval acek acek'
local notation:40 acek:41 "⤳ₐ⋆" acek':41 => aevals acek acek'

inductive aeval : ACEK → ACEK → Prop where
  | force {σ fs m}       : ⟨.com (.force (.thunk m)), σ, fs⟩  ⤳ₐ ⟨m, σ, fs⟩
  | force' {σ fs x}      : ⟨.com (.force (.var x)), σ, fs⟩    ⤳ₐ ⟨.com (.force (σ x)), σ, fs⟩
  | lam {σ fs m v}       : ⟨.com (.lam m), σ, .app v :: fs⟩   ⤳ₐ ⟨m, v +: σ, renameFₐ succ fs⟩
  | app {σ fs n v}       : ⟨.com (.app n v), σ, fs⟩           ⤳ₐ ⟨.com n, σ, .cons (.app v) fs⟩
  | ret {σ fs m v}       : ⟨.com (.ret v), σ, .letin m :: fs⟩ ⤳ₐ ⟨m, v +: σ, renameFₐ succ fs⟩
  | letin {σ fs n m}     : ⟨.letin n m, σ, fs⟩                ⤳ₐ ⟨.com n, σ, .cons (.letin m) fs⟩
  | case₁ {σ fs v m₁ m₂} : ⟨.case (.inl v) m₁ m₂, σ, fs⟩      ⤳ₐ ⟨m₁, v +: σ, renameFₐ succ fs⟩
  | case₂ {σ fs v m₁ m₂} : ⟨.case (.inr v) m₁ m₂, σ, fs⟩      ⤳ₐ ⟨m₂, v +: σ, renameFₐ succ fs⟩
  | case' {σ fs m₁ m₂ x} : ⟨.case (.var x) m₁ m₂, σ, fs⟩      ⤳ₐ ⟨.case (σ x) m₁ m₂, σ, fs⟩

inductive aevals : ACEK → ACEK → Prop where
  | refl {m σ fs} : ⟨m, σ, fs⟩ ⤳ₐ⋆ ⟨m, σ, fs⟩
  | trans {m₁ m₂ m₃ σ₁ σ₂ σ₃ fs₁ fs₂ fs₃} :
    ⟨m₁, σ₁, fs₁⟩ ⤳ₐ  ⟨m₂, σ₂, fs₂⟩ →
    ⟨m₂, σ₂, fs₂⟩ ⤳ₐ⋆ ⟨m₃, σ₃, fs₃⟩ →
    ⟨m₁, σ₁, fs₁⟩ ⤳ₐ⋆ ⟨m₃, σ₃, fs₃⟩
end

notation:40 acek:41 "⤳ₐ" acek':41 => aeval acek acek'
notation:40 acek:41 "⤳ₐ⋆" acek':41 => aevals acek acek'

theorem compositionality' {m σ fs k} : ⟨k [ m ], σ, fs⟩ ⤳ₐ⋆ ⟨.com m, σ, KFₐ k ++ fs⟩ := by
  induction k generalizing m
  case nil => exact .refl
  case app ih => exact .trans' ih aeval.app.aevals
  case letin => exact aeval.letin.aevals

theorem compositionality {m k σ fs} : ⟨compKCfg k m, σ, fs⟩ ⤳ₐ⋆ ⟨m, σ, KFₐ k ++ fs⟩ := by
  mutual_induction m
  case com => exact compositionality'
  case letin ih => simp; refine .trans .letin ?_; sorry
  case case ihm₁ ihm₂ => simp; sorry

theorem equivalence {m m' σ σ' fs fs'} (r : ⟨m, σ, fs⟩ ⤳ ⟨m', σ', fs'⟩) :
  ∀ fsₐ, ∃ fsₐ', ⟨⟦ m ⟧ₘ (FK fs), ⟦ σ ⟧ₛ, fsₐ⟩ ⤳ₐ⋆ ⟨⟦ m' ⟧ₘ (FK fs'), ⟦ σ' ⟧ₛ, fsₐ'⟩ := by
  intro fsₐ
  generalize e : (m, σ, fs) = cek, e' : (m', σ', fs') = cek' at r
  induction r
  all_goals injection e with em e; injection e with eσ ef; subst em eσ ef
  all_goals injection e' with em' e'; injection e' with eσ' ef'; subst em' eσ' ef'
  case force =>
    simp; exists fsₐ
    refine .trans' compositionality' ?_
    refine .trans .force ?_
    have e : FK fs' = compKK (FK fs') .nil := by rfl
    rw [e, ← compA, ← e]
    sorry
  case force' =>
    simp; exists fsₐ
    refine .trans' compositionality' ?_
    refine .trans .force' ?_
    rw [Alookup]
    sorry
  case lam fs _ =>
    rw [Acons]; simp; exists renameFₐ succ fsₐ
    refine .trans' compositionality' ?_
    refine .trans .app ?_
    refine .trans .lam ?_
    have e : FK (renameF succ fs) = compKK (FK (renameF succ fs)) .nil := by rfl
    rw [e, ← compA]
    sorry
  case app => exact ⟨_, .refl⟩
  case ret v => rw [Acons, renameFK]; exact ⟨_, .trans .letin (.trans .ret .refl)⟩
  case letin => simp; exists fsₐ; exact .refl
  case case₁ => rw [Acons, renameFK]; exact ⟨_, .trans .case₁ .refl⟩
  case case₂ => rw [Acons, renameFK]; exact ⟨_, .trans .case₂ .refl⟩
  case case' => exact ⟨_, aeval.case'.aevals⟩

theorem equivalence' {m m' σ σ' fs fs'} (r : ⟨m, σ, fs⟩ ⤳ ⟨m', σ', fs'⟩) :
  ⟨⟦ m ⟧ₘ .nil, ⟦ σ ⟧ₛ, FFₐ fs⟩ ⤳ₐ⋆ ⟨⟦ m' ⟧ₘ .nil, ⟦ σ' ⟧ₛ, FFₐ fs'⟩ := by
  generalize e : (m, σ, fs) = cek, e' : (m', σ', fs') = cek' at r
  induction r
  all_goals injection e with em e; injection e with eσ ef; subst em eσ ef
  all_goals injection e' with em' e'; injection e' with eσ' ef'; subst em' eσ' ef'
  all_goals try rw [Acons, renameFFₐ]
  case force | force' | lam | ret | case₁ | case₂ | case' =>
    apply aeval.aevals; constructor
  case app v =>
    have e : K.app (⟦ v ⟧ᵥ) .nil = compKK (K.app (⟦ v ⟧ᵥ) .nil) .nil := rfl
    simp; rw [e, ← compA]; exact compositionality
  case letin m =>
    have e : K.letin (⟦ m ⟧ₘ .nil) = compKK (K.letin (⟦ m ⟧ₘ .nil)) .nil := rfl
    simp; rw [e, ← compA]; exact compositionality
-/
