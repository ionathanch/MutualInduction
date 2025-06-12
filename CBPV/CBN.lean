import CBPV.Typing
import CBPV.CK

open Nat

namespace CBN

/-* Types and terms *-/

inductive SType : Type where
  | Unit : SType
  | Arr : SType → SType → SType
  | Sum : SType → SType → SType
open SType

inductive Term : Type where
  | var : Nat → Term
  | unit : Term
  | lam : Term → Term
  | app : Term → Term → Term
  | inl : Term → Term
  | inr : Term → Term
  | case : Term → Term → Term → Term
open Term

/-* Renaming and substitution *-/

@[simp]
def rename (ξ : Nat → Nat) : Term → Term
  | var x => var (ξ x)
  | unit => unit
  | lam t => lam (rename (lift ξ) t)
  | app t u => app (rename ξ t) (rename ξ u)
  | inl t => inl (rename ξ t)
  | inr t => inr (rename ξ t)
  | case s t u => case (rename ξ s) (rename (lift ξ) t) (rename (lift ξ) u)

@[simp]
def up (σ : Nat → Term) : Nat → Term :=
  var 0 +: (rename succ ∘ σ)
prefix:95 "⇑" => up

@[simp]
def subst (σ : Nat → Term) : Term → Term
  | var x => σ x
  | unit => unit
  | lam t => lam (subst (⇑ σ) t)
  | app t u => app (subst σ t) (subst σ u)
  | inl t => inl (subst σ t)
  | inr t => inr (subst σ t)
  | case s t u => case (subst σ s) (subst (⇑ σ) t) (subst (⇑ σ) u)

/-* Contexts and membership *-/

inductive Ctxt : Type where
  | nil : Ctxt
  | cons : Ctxt → SType → Ctxt
notation:50 "⬝" => Ctxt.nil
infixl:50 "∷" => Ctxt.cons

inductive In : Nat → SType → Ctxt → Prop where
  | here {Γ A} : In 0 A (Γ ∷ A)
  | there {Γ x A B} : In x A Γ → In (succ x) A (Γ ∷ B)
notation:40 Γ:41 "∋ₛ" x:41 "∶" A:41 => In x A Γ

/-* Typing *-/
section
set_option hygiene false
local notation:40 Γ:41 "⊢ₛ" t:41 "∶" A:41 => Wt Γ t A
inductive Wt : Ctxt → Term → SType → Prop where
  | var {Γ x A} :
    Γ ∋ₛ x ∶ A →
    --------------
    Γ ⊢ₛ var x ∶ A
  | unit {Γ} : Γ ⊢ₛ unit ∶ Unit
  | lam {Γ t A} {B : SType} :
    Γ ∷ A ⊢ₛ t ∶ B →
    --------------------
    Γ ⊢ₛ lam t ∶ Arr A B
  | app {Γ t u A B} :
    Γ ⊢ₛ t ∶ Arr A B →
    Γ ⊢ₛ u ∶ A →
    ----------------
    Γ ⊢ₛ app t u ∶ B
  | inl {Γ t} {A₁ A₂ : SType} :
    Γ ⊢ₛ t ∶ A₁ →
    ----------------------
    Γ ⊢ₛ inl t ∶ Sum A₁ A₂
  | inr {Γ t} {A₁ A₂ : SType} :
    Γ ⊢ₛ t ∶ A₂ →
    ----------------------
    Γ ⊢ₛ inr t ∶ Sum A₁ A₂
  | case {Γ s t u A₁ A₂} {B : SType} :
    Γ ⊢ₛ s ∶ Sum A₁ A₂ →
    Γ ∷ A₁ ⊢ₛ t ∶ B →
    Γ ∷ A₂ ⊢ₛ u ∶ B →
    -------------------
    Γ ⊢ₛ case s t u ∶ B
end
notation:40 Γ:41 "⊢ₛ" v:41 "∶" A:41 => Wt Γ v A

/-* CK machine semantics *-/

inductive F : Type where
  | app : Term → F
  | case : Term → Term → F

def K := List F
def CK := Term × K

section
set_option hygiene false
local infix:40 "⤳ₙ" => Step
inductive Step : CK → CK → Prop where
  | β {t u k} :      ⟨lam t, .app u :: k⟩     ⤳ₙ ⟨subst (u +: var) t, k⟩
  | ιl {s t u k} :   ⟨inl s, .case t u :: k ⟩ ⤳ₙ ⟨subst (s +: var) t, k⟩
  | ιr {s t u k} :   ⟨inr s, .case t u :: k ⟩ ⤳ₙ ⟨subst (s +: var) u, k⟩
  | app {t u k} :    ⟨app t u, k⟩             ⤳ₙ ⟨t, .app u :: k⟩
  | case {s t u k} : ⟨case s t u, k⟩          ⤳ₙ ⟨s, .case t u :: k⟩
end
infix:40 "⤳ₙ" => Step

end CBN

/-*-------------------------
  Call by name translation
-------------------------*-/

/-* Translation of types *-/
section
set_option hygiene false
local notation:40 "⟦" A:41 "⟧ᵀ" => transType A
@[simp]
def transType : CBN.SType → ComType
  | .Unit => .F .Unit
  | .Sum A₁ A₂ => .F (.Sum (.U (⟦ A₁ ⟧ᵀ)) (.U (⟦ A₂ ⟧ᵀ)))
  | .Arr A B => .Arr (.U (⟦ A ⟧ᵀ)) (⟦ B ⟧ᵀ)
end
notation:40 "⟦" A:41 "⟧ᵀ" => transType A

/-* Translation of contexts *-/
section
set_option hygiene false
local notation:40 "⟦" Γ:41 "⟧ᶜ" => transCtxt Γ
@[simp]
def transCtxt : CBN.Ctxt → Ctxt
  | .nil => .nil
  | .cons Γ A => .cons (⟦ Γ ⟧ᶜ) (.U (⟦ A ⟧ᵀ))
end
notation:40 "⟦" Γ:41 "⟧ᶜ" => transCtxt Γ

/-* Translation of terms *-/
section
set_option hygiene false
local notation:40 "⟦" t:41 "⟧ᵗ" => transTerm t
@[simp]
def transTerm : CBN.Term → Com
  | .var s => .force (.var s)
  | .unit => .ret .unit
  | .lam t => .lam (⟦ t ⟧ᵗ)
  | .app t u => .app (⟦ t ⟧ᵗ) (.thunk (⟦ u ⟧ᵗ))
  | .inl t => .ret (.inl (.thunk (⟦ t ⟧ᵗ)))
  | .inr t => .ret (.inr (.thunk (⟦ t ⟧ᵗ)))
  | .case s t u =>
    .letin (⟦ s ⟧ᵗ)
      (.case (.var 0)
        (renameCom (lift succ) (⟦ t ⟧ᵗ))
        (renameCom (lift succ) (⟦ u ⟧ᵗ)))
end
notation:40 "⟦" t:41 "⟧ᵗ" => transTerm t

@[simp] def transSubst' (σ : Nat → CBN.Term) : Nat → Val := λ x ↦ .thunk (⟦ σ x ⟧ᵗ)
notation:40 "⟦" σ:41 "⟧ˢ" => transSubst' σ

/-* Translation of stacks *-/
section
set_option hygiene false
local notation:40 "⟦" k:41 "⟧ᴷ" => transK k
@[simp]
def transK : CBN.K → K
  | [] => []
  | .app u :: k   => .app (.thunk (⟦ u ⟧ᵗ)) :: (⟦ k ⟧ᴷ)
  | .case t u :: k => .letin (.case (.var 0)
                        (renameCom (lift succ) (⟦ t ⟧ᵗ))
                        (renameCom (lift succ) (⟦ u ⟧ᵗ))) :: (⟦ k ⟧ᴷ)
end
notation:40 "⟦" k:41 "⟧ᴷ" => transK k

/-* Translation of terms with arbitrary π-expansion *-/
section
set_option hygiene false
local infix:40 "↦ₙ" => transTerm'
inductive transTerm' : CBN.Term → Com → Prop where
  | var {s} : .var s ↦ₙ .force (.var s)
  | unit : .unit ↦ₙ .ret .unit
  | lam {t m} : t ↦ₙ m → .lam t ↦ₙ .lam m
  | app {t u m n} : t ↦ₙ m → u ↦ₙ n → .app t u ↦ₙ .app m (.thunk n)
  | inl {t m} : t ↦ₙ m → .inl t ↦ₙ .ret (.inl (.thunk m))
  | inr {t m} : t ↦ₙ m → .inr t ↦ₙ .ret (.inr (.thunk m))
  | case {s t u ms mt mu} : s ↦ₙ ms → t ↦ₙ mt → u ↦ₙ mu →
    .case s t u ↦ₙ
      .letin ms
        (.case (.var 0)
          (renameCom (lift succ) mt)
          (renameCom (lift succ) mu))
  | ft {t m} : t ↦ₙ m → t ↦ₙ .force (.thunk m)
end
infix:40 "↦ₙ" => transTerm'

theorem transTransTerm {t} : t ↦ₙ (⟦ t ⟧ᵗ) := by
  induction t <;> constructor <;> assumption

/-*---------------------------------------
  Preservation properties of translation
---------------------------------------*-/

/-* Translation is type preserving *-/

theorem presIn {x A Γ} (h : CBN.In x A Γ) : (⟦ Γ ⟧ᶜ) ∋ x ∶ .U (⟦ A ⟧ᵀ) := by
  induction h <;> constructor; assumption

theorem preservation {Γ t A} (h : Γ ⊢ₛ t ∶ A) : (⟦ Γ ⟧ᶜ) ⊢ (⟦ t ⟧ᵗ) ∶ (⟦ A ⟧ᵀ) := by
  induction h
  case var ih => exact .force (.var (presIn ih))
  case unit => exact .ret .unit
  case lam ih => exact .lam ih
  case app iht ihu => exact .app iht (.thunk ihu)
  case inl ih => exact .ret (.inl (.thunk ih))
  case inr ih => exact .ret (.inr (.thunk ih))
  case case ihs iht ihu =>
    exact .letin ihs (.case (.var .here) (wtWeakenCom₂ iht) (wtWeakenCom₂ ihu))

/-* Translation commutes with renaming and substitution *-/

theorem transRename {ξ t m} (h : t ↦ₙ m) : CBN.rename ξ t ↦ₙ renameCom ξ m := by
  induction h generalizing ξ
  case var | unit | inl | inr | app | lam | ft => constructor <;> apply_assumption
  case case ihs iht ihu =>
    simp [-lift]; rw [renameLiftLiftRename, renameLiftLiftRename]
    exact .case ihs iht ihu

theorem transUp {σ : Nat → CBN.Term} {σ' : Nat → Val}
  (h : ∀ x, σ x ↦ₙ .force (σ' x)) : ∀ x, (⇑ σ) x ↦ₙ .force ((⇑ σ') x) := by
  have e {ξ v} : .force (renameVal ξ v) = renameCom ξ (.force v) := rfl
  intro n; cases n
  case zero => exact .var
  case succ n => simp; rw [e]; exact transRename (h n)

theorem transSubst {σ σ' t} (h : ∀ x, σ x ↦ₙ .force (σ' x)) : CBN.subst σ t ↦ₙ substCom σ' (⟦t⟧ᵗ) := by
  induction t generalizing σ σ'
  case var => exact h _
  case unit | inl | inr | app => constructor <;> apply_rules
  case lam ih => exact .lam (ih (transUp h))
  case case ihs iht ihu =>
    simp [-up, -lift]; rw [← renameUpLiftSubst, ← renameUpLiftSubst]
    exact .case (ihs h) (iht (transUp h)) (ihu (transUp h))

theorem transSubstSingle {t u} : CBN.subst (u +: .var) t ↦ₙ (⟦t⟧ᵗ) ⦃ Val.thunk (⟦ u ⟧ᵗ) +: .var ⦄ := by
  refine transSubst (λ n ↦ ?_); cases n <;> constructor; exact transTransTerm

/-* Translation preserves machine semantics *-/

theorem simulation {t u k k'} (r : ⟨t, k⟩ ⤳ₙ ⟨u, k'⟩) : ∃ m, ⟨⟦ t ⟧ᵗ, ⟦ k ⟧ᴷ⟩ ⤳⋆ ⟨m, ⟦ k' ⟧ᴷ⟩ ∧ u ↦ₙ m := by
  generalize et : (t, k)  = ck  at r
  generalize eu : (u, k') = ck' at r
  induction r
  all_goals injection et with et ek; subst et ek
  all_goals injection eu with eu ek; subst eu ek
  case β t u => exact ⟨⟦ t ⟧ᵗ ⦃ .thunk (⟦ u ⟧ᵗ) ⦄, .once .β, transSubstSingle⟩
  case ιl s t _ =>
    refine ⟨⟦ t ⟧ᵗ ⦃ .thunk (⟦ s ⟧ᵗ)⦄, ?_, transSubstSingle⟩
    calc
      _ ⤳ _ := .ζ
      _ ⤳ _ := by simp [-lift]; exact .ιl
      _ = _ := by
        have e {σ} : (.var 0 +: renameVal succ ∘ σ) = ⇑ σ := rfl
        rw [e, ← substUnion, substDropCom₂]
  case ιr s _ u =>
    refine ⟨⟦ u ⟧ᵗ ⦃ .thunk (⟦ s ⟧ᵗ)⦄, ?_, transSubstSingle⟩
    calc
      _ ⤳ _ := .ζ
      _ ⤳ _ := by simp [-lift]; exact .ιr
      _ = _ := by
        have e {σ} : (.var 0 +: renameVal succ ∘ σ) = ⇑ σ := rfl
        rw [e, ← substUnion, substDropCom₂]
  case app => exact ⟨_, .once .app, transTransTerm⟩
  case case => exact ⟨_, .once .letin, transTransTerm⟩
