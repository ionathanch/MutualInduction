import CBPV.Typing
import CBPV.CK

open Nat

namespace CBV

/-* Types, values, and terms *-/

inductive VType : Type where
  | Unit : VType
  | Arr : VType → VType → VType
  | Sum : VType → VType → VType
  | Pair : VType → VType → VType
open VType

mutual
inductive Value : Type where
  | var : Nat → Value
  | unit : Value
  | lam : Term → Value
  | inl : Value → Value
  | inr : Value → Value
  | pair : Value → Value → Value

inductive Term : Type where
  | val : Value → Term
  | app : Term → Term → Term
  | case : Term → Term → Term → Term
  | fst : Term → Term
  | snd : Term → Term
end
open Term
open Value

/-* Renaming and substitution *-/

mutual
@[simp]
def renameVal (ξ : Nat → Nat) : Value → Value
  | var x => var (ξ x)
  | unit => unit
  | lam t => lam (rename (lift ξ) t)
  | inl v => inl (renameVal ξ v)
  | inr v => inr (renameVal ξ v)
  | pair v w => pair (renameVal ξ v) (renameVal ξ w)

@[simp]
def rename (ξ : Nat → Nat) : Term → Term
  | val v => val (renameVal ξ v)
  | app t u => app (rename ξ t) (rename ξ u)
  | case s t u => case (rename ξ s) (rename (lift ξ) t) (rename (lift ξ) u)
  | fst t => fst (rename ξ t)
  | snd t => snd (rename ξ t)
end

@[simp]
def up (σ : Nat → Value) : Nat → Value :=
  var 0 +: (renameVal succ ∘ σ)
prefix:95 "⇑" => up

mutual
@[simp]
def substVal (σ : Nat → Value) : Value → Value
  | var x => σ x
  | unit => unit
  | lam t => lam (subst (⇑ σ) t)
  | inl v => inl (substVal σ v)
  | inr v => inr (substVal σ v)
  | pair v w => pair (substVal σ v) (substVal σ w)

@[simp]
def subst (σ : Nat → Value) : Term → Term
  | val v => val (substVal σ v)
  | app t u => app (subst σ t) (subst σ u)
  | case s t u => case (subst σ s) (subst (⇑ σ) t) (subst (⇑ σ) u)
  | fst t => fst (subst σ t)
  | snd t => snd (subst σ t)
end

/-* Contexts and membership *-/

inductive Ctxt : Type where
  | nil : Ctxt
  | cons : Ctxt → VType → Ctxt
notation:50 "⬝" => Ctxt.nil
infixl:50 "∷" => Ctxt.cons

inductive In : Nat → VType → Ctxt → Prop where
  | here {Γ A} : In 0 A (Γ ∷ A)
  | there {Γ x A B} : In x A Γ → In (succ x) A (Γ ∷ B)
notation:40 Γ:41 "∋ₛ" x:41 "∶" A:41 => In x A Γ

/-* Typing *-/

section
set_option hygiene false
local notation:40 Γ:41 "⊢ᵥ" v:41 "∶" A:41 => WtVal Γ v A
local notation:40 Γ:41 "⊢ₛ" t:41 "∶" A:41 => Wt Γ t A

mutual
inductive WtVal : Ctxt → Value → VType → Prop where
  | var {Γ x A} :
    Γ ∋ₛ x ∶ A →
    --------------
    Γ ⊢ᵥ var x ∶ A
  | unit {Γ} : Γ ⊢ᵥ unit ∶ Unit
  | lam {Γ t A} {B : VType} :
    Γ ∷ A ⊢ₛ t ∶ B →
    --------------------
    Γ ⊢ᵥ lam t ∶ Arr A B
  | inl {Γ v} {A₁ A₂ : VType} :
    Γ ⊢ᵥ v ∶ A₁ →
    ----------------------
    Γ ⊢ᵥ inl v ∶ Sum A₁ A₂
  | inr {Γ v} {A₁ A₂ : VType} :
    Γ ⊢ᵥ v ∶ A₂ →
    ----------------------
    Γ ⊢ᵥ inr v ∶ Sum A₁ A₂
  | pair {Γ v w} {A₁ A₂ : VType} :
    Γ ⊢ᵥ v ∶ A₁ →
    Γ ⊢ᵥ w ∶ A₂ →
    --------------------------
    Γ ⊢ᵥ pair v w ∶ Pair A₁ A₂

inductive Wt : Ctxt → Term → VType → Prop where
  | val {Γ v A} :
    Γ ⊢ᵥ v ∶ A →
    --------------
    Γ ⊢ₛ val v ∶ A
  | app {Γ t u A B} :
    Γ ⊢ₛ t ∶ Arr A B →
    Γ ⊢ₛ u ∶ A →
    ----------------
    Γ ⊢ₛ app t u ∶ B
  | case {Γ s t u A₁ A₂} {B : VType} :
    Γ ⊢ₛ s ∶ Sum A₁ A₂ →
    Γ ∷ A₁ ⊢ₛ t ∶ B →
    Γ ∷ A₂ ⊢ₛ u ∶ B →
    -------------------
    Γ ⊢ₛ case s t u ∶ B
  | fst {Γ t A₁ A₂} :
    Γ ⊢ₛ t ∶ Pair A₁ A₂ →
    ---------------
    Γ ⊢ₛ fst t ∶ A₁
  | snd {Γ t A₁ A₂} :
    Γ ⊢ₛ t ∶ Pair A₁ A₂ →
    ---------------
    Γ ⊢ₛ snd t ∶ A₂
end
end

notation:40 Γ:41 "⊢ᵥ" v:41 "∶" A:41 => WtVal Γ v A
notation:40 Γ:41 "⊢ₛ" t:41 "∶" A:41 => Wt Γ t A

/-* CK machine semantics *-/

inductive F : Type where
  | app₁ : Term → F
  | app₂ : Value → F
  | case : Term → Term → F
  | fst : F
  | snd : F

def K := List F
def CK := Term × K

section
set_option hygiene false
local infix:40 "⤳ᵥ" => Step
inductive Step : CK → CK → Prop where
  | β  {t v k} :     ⟨.val v, .app₂ (.lam t) :: k⟩  ⤳ᵥ ⟨subst (v +: var) t, k⟩
  | ιl {v t u k} :   ⟨.val (inl v), .case t u :: k⟩ ⤳ᵥ ⟨subst (v +: var) t, k⟩
  | ιr {v t u k} :   ⟨.val (inr v), .case t u :: k⟩ ⤳ᵥ ⟨subst (v +: var) u, k⟩
  | π1 {v w k} :     ⟨.val (pair v w), .fst :: k⟩   ⤳ᵥ ⟨.val v, k⟩
  | π2 {v w k} :     ⟨.val (pair v w), .snd :: k⟩   ⤳ᵥ ⟨.val w, k⟩
  | app₁ {t u k} :   ⟨app t u, k⟩                   ⤳ᵥ ⟨t, .app₁ u :: k⟩
  | app₂ {t v k} :   ⟨.val v, .app₁ t :: k⟩         ⤳ᵥ ⟨t, .app₂ v :: k⟩
  | case {s t u k} : ⟨case s t u, k⟩                ⤳ᵥ ⟨s, .case t u :: k⟩
  | fst {t k} :      ⟨fst t, k⟩                     ⤳ᵥ ⟨t, .fst :: k⟩
  | snd {t k} :      ⟨snd t, k⟩                     ⤳ᵥ ⟨t, .snd :: k⟩
end
infix:40 "⤳ᵥ" => Step

end CBV

/-*--------------------------
  Call by value translation
--------------------------*-/

/-* Translation of types *-/

section
set_option hygiene false
local notation:40 "⟦" A:41 "⟧ᵀ" => transType A
@[simp]
def transType : CBV.VType → ValType
  | .Unit => .Unit
  | .Sum A₁ A₂ => .Sum (⟦ A₁ ⟧ᵀ) (⟦ A₂ ⟧ᵀ)
  | .Arr A B => .U (.Arr (⟦ A ⟧ᵀ) (.F (⟦ B ⟧ᵀ)))
  | .Pair A₁ A₂ => .U (.Prod (.F (⟦ A₁ ⟧ᵀ)) (.F (⟦ A₂ ⟧ᵀ)))
end
notation:40 "⟦" A:41 "⟧ᵀ" => transType A

/-* Translation of contexts *-/

section
set_option hygiene false
local notation:40 "⟦" Γ:41 "⟧ᶜ" => transCtxt Γ
@[simp]
def transCtxt : CBV.Ctxt → Ctxt
  | .nil => .nil
  | .cons Γ A => .cons (⟦ Γ ⟧ᶜ) (⟦ A ⟧ᵀ)
end
notation:40 "⟦" Γ:41 "⟧ᶜ" => transCtxt Γ

/-* Translation of values and terms *-/

section
set_option hygiene false
local notation:40 "⟦" v:41 "⟧ᵛ" => transValue v
local notation:40 "⟦" t:41 "⟧ᵗ" => transTerm t

mutual
@[simp]
def transValue : CBV.Value → Val
  | .var x => .var x
  | .unit => .unit
  | .lam t => .thunk (.lam (⟦ t ⟧ᵗ))
  | .inl v => .inl (⟦ v ⟧ᵛ)
  | .inr v => .inr (⟦ v ⟧ᵛ)
  | .pair v w => .thunk (.prod (.ret (⟦ v ⟧ᵛ)) (.ret (⟦ w ⟧ᵛ)))

@[simp]
def transTerm : CBV.Term → Com
  | .val v => .ret (⟦ v ⟧ᵛ)
  | .app t u =>
    .letin (⟦ t ⟧ᵗ)
      (.letin (renameCom succ (⟦ u ⟧ᵗ))
        (.app (.force (.var 1)) (.var 0)))
  | .case s t u =>
    .letin (⟦ s ⟧ᵗ)
      (.case (.var 0)
        (renameCom (lift succ) (⟦ t ⟧ᵗ))
        (renameCom (lift succ) (⟦ u ⟧ᵗ)))
  | .fst t => .letin (⟦ t ⟧ᵗ) (.fst (.force (.var 0)))
  | .snd t => .letin (⟦ t ⟧ᵗ) (.snd (.force (.var 0)))
end
end

notation:40 "⟦" v:41 "⟧ᵛ" => transValue v
notation:40 "⟦" t:41 "⟧ᵗ" => transTerm t

@[simp] def transSubst' (σ : Nat → CBV.Value) : Nat → Val := λ x ↦ ⟦ σ x ⟧ᵛ
notation:40 "⟦" σ:41 "⟧ˢ" => transSubst' σ

/-* Translation of stacks *-/

section
set_option hygiene false
local notation:40 "⟦" k:41 "⟧ᴷ" => transK k
@[simp]
def transK : CBV.K → K
  | [] => []
  | .app₁ u :: k   => .letin (.letin (renameCom succ (⟦ u ⟧ᵗ))
                        (.app (.force (.var 1)) (.var 0))) :: (⟦ k ⟧ᴷ)
  | .app₂ v :: k   => .letin (.app (.force (renameVal succ (⟦ v ⟧ᵛ))) (.var 0)) :: (⟦ k ⟧ᴷ)
  | .case t u :: k => .letin (.case (.var 0)
                        (renameCom (lift succ) (⟦ t ⟧ᵗ))
                        (renameCom (lift succ) (⟦ u ⟧ᵗ))) :: (⟦ k ⟧ᴷ)
  | .fst :: k      => .letin (.fst (.force (.var 0))) :: (⟦ k ⟧ᴷ)
  | .snd :: k      => .letin (.snd (.force (.var 0))) :: (⟦ k ⟧ᴷ)
end
notation:40 "⟦" k:41 "⟧ᴷ" => transK k

/-*---------------------------------------
  Preservation properties of translation
---------------------------------------*-/

/-* Translation is type preserving *-/

theorem presIn {x A Γ} (h : CBV.In x A Γ) : (⟦ Γ ⟧ᶜ) ∋ x ∶ (⟦ A ⟧ᵀ) := by
  induction h <;> constructor; assumption

theorem preservation {Γ A} :
  (∀ {v}, Γ ⊢ᵥ v ∶ A → (⟦ Γ ⟧ᶜ) ⊢ (⟦ v ⟧ᵛ) ∶ (⟦ A ⟧ᵀ)) ∧
  (∀ {t}, Γ ⊢ₛ t ∶ A → (⟦ Γ ⟧ᶜ) ⊢ (⟦ t ⟧ᵗ) ∶ .F (⟦ A ⟧ᵀ)) := by
  refine ⟨λ h ↦ ?val, λ h ↦ ?term⟩
  mutual_induction h, h
  case var ih => exact .var (presIn ih)
  case unit => exact .unit
  case lam ih => exact .thunk (.lam ih)
  case inl ih => exact .inl ih
  case inr ih => exact .inr ih
  case pair ihv ihw => exact (.thunk (.prod (.ret ihv) (.ret ihw)))
  case val ih => exact .ret ih
  case app iht ihu =>
    exact .letin iht
      (.letin (wtWeakenCom ihu)
        (.app (.force (.var (.there .here))) (.var .here)))
  case case ihs iht ihu =>
    exact .letin ihs (.case (.var .here) (wtWeakenCom₂ iht) (wtWeakenCom₂ ihu))
  case fst ih => exact .letin ih (.fst (.force (.var .here)))
  case snd ih => exact .letin ih (.snd (.force (.var .here)))

/-* Translation commutes with renaming and substitution *-/

theorem transRename {ξ} :
  (∀ {v}, renameVal ξ (⟦ v ⟧ᵛ) = (⟦ CBV.renameVal ξ v ⟧ᵛ)) ∧
  (∀ {t}, renameCom ξ (⟦ t ⟧ᵗ) = (⟦ CBV.rename ξ t ⟧ᵗ)) := by
  refine ⟨λ {v} ↦ ?val, λ {t} ↦ ?term⟩
  mutual_induction v, t generalizing ξ
  case var n => cases n <;> rfl
  case unit => rfl
  case lam ih | inl ih | inr ih | val ih | fst ih | snd ih => simp [ih]
  case pair ihv ihw => simp [ihv, ihw]
  case app iht ihu => simp [iht, ← ihu, renameLiftRename]
  case case ihs iht ihu =>
    simp [-lift, ihs, ← iht, ← ihu, renameLiftLiftRename]; rfl

def transRenameVal {ξ v} := (transRename (ξ := ξ)).left (v := v)
def transRenameCom {ξ t} := (transRename (ξ := ξ)).right (t := t)

theorem transUp {σ m} : substCom (⇑ (⟦ σ ⟧ˢ)) m = substCom (⟦ ⇑ σ ⟧ˢ) m := by
  apply substComExt; intro n; cases n <;> simp [transRenameVal]

theorem transSubst {σ} :
  (∀ {v}, ((⟦ v ⟧ᵛ) ⦃ ⟦ σ ⟧ˢ ⦄) = (⟦ CBV.substVal σ v ⟧ᵛ)) ∧
  (∀ {t}, ((⟦ t ⟧ᵗ) ⦃ ⟦ σ ⟧ˢ ⦄) = (⟦ CBV.subst σ t ⟧ᵗ)) := by
  refine ⟨λ {v} ↦ ?val, λ {t} ↦ ?term⟩
  mutual_induction v, t generalizing σ
  case var n => cases n <;> simp
  case unit => rfl
  case lam ih => simp [-lift, -up, ← ih, transUp]
  case inl ih | inr ih | val ih | fst ih | snd ih => simp [ih]
  case pair ihv ihw => simp [ihv, ihw]
  case app iht ihu => simp [-lift, -up, iht, ← ihu, ← renameUpSubst]; simp
  case case ihs iht ihu =>
    simp [-lift, -up, -CBV.up, ihs, ← iht, ← ihu]; repeat' constructor
    all_goals rw [← transUp, ← renameUpLiftSubst]

def transSubstVal {σ v} := (transSubst (σ := σ)).left (v := v)
def transSubstCom {σ t} := (transSubst (σ := σ)).right (t := t)

/-* Translation preserves machine semantics *-/

theorem simulation {t u k k'} (r : ⟨t, k⟩ ⤳ᵥ ⟨u, k'⟩) : ⟨⟦ t ⟧ᵗ, ⟦ k ⟧ᴷ⟩ ⤳⋆ ⟨⟦ u ⟧ᵗ, ⟦ k' ⟧ᴷ⟩ := by
  generalize et : (t, k)  = ck  at r
  generalize eu : (u, k') = ck' at r
  induction r
  all_goals injection et with et ek; subst et ek
  all_goals injection eu with eu ek; subst eu ek
  case β v =>
    calc
      _ ⤳ _ := Step.ζ
      _ ⤳ _ := by simp [-lift, -up]; exact Step.app
      _ ⤳ _ := Step.π
      _ ⤳ _ := Step.β
      _ = _ := by
        rw [← substUnion, substDropCom₂, ← transSubstCom, substComExt]
        intro n; cases n <;> rfl
  case ιl =>
    calc
      _ ⤳ _ := Step.ζ
      _ ⤳ _ := by simp [-lift, -up]; exact Step.ιl
      _ = _ := by
        rw [← substUnion, substDrop₂, ← transSubstCom, substComExt]
        intro n; cases n <;> rfl
  case ιr =>
    calc
      _ ⤳ _ := Step.ζ
      _ ⤳ _ := by simp [-lift, -up]; exact Step.ιr
      _ = _ := by
        rw [← substUnion, substDrop₂, ← transSubstCom, substComExt]
        intro n; cases n <;> rfl
  case π1 =>
    simp
    calc
      _ ⤳ _ := Step.ζ
      _ ⤳ _ := by simp; exact Step.fst
      _ ⤳ _ := Step.π
      _ ⤳ _ := Step.π1
  case π2 =>
    simp
    calc
      _ ⤳ _ := Step.ζ
      _ ⤳ _ := by simp; exact Step.snd
      _ ⤳ _ := Step.π
      _ ⤳ _ := Step.π2
  case app₁ => exact .once .letin
  case app₂ =>
    calc
      _ ⤳ _ := Step.ζ
      _ ⤳ _ := by simp; exact Step.letin
      _ = _ := by simp [← substDropCom]
  case case => exact .once .letin
  case fst => exact .once .letin
  case snd => exact .once .letin
