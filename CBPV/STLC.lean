import CBPV.Typing

open Nat

namespace STLC

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

end STLC

/-*--------------------------
  Call by value translation
--------------------------*-/

namespace CBV

/-* Translation of types *-/
section
set_option hygiene false
local notation:40 "⟦" A:41 "⟧ᵀ" => transType A
def transType : STLC.SType → ValType
  | .Unit => .Unit
  | .Sum A₁ A₂ => .Sum (⟦ A₁ ⟧ᵀ) (⟦ A₂ ⟧ᵀ)
  | .Arr A B => .U (.Arr (⟦ A ⟧ᵀ) (.F (⟦ B ⟧ᵀ)))
end
local notation:40 "⟦" A:41 "⟧ᵀ" => transType A

/-* Translation of contexts *-/
section
set_option hygiene false
local notation:40 "⟦" Γ:41 "⟧ᶜ" => transCtxt Γ
def transCtxt : STLC.Ctxt → Ctxt
  | .nil => .nil
  | .cons Γ A => .cons (⟦ Γ ⟧ᶜ) (⟦ A ⟧ᵀ)
end
local notation:40 "⟦" Γ:41 "⟧ᶜ" => transCtxt Γ

/-* Translation of terms *-/
section
set_option hygiene false
local notation:40 "⟦" t:41 "⟧ᵗ" => transTerm t
def transTerm : STLC.Term → Com
  | .var s => .ret (.var s)
  | .unit => .ret .unit
  | .lam t => .ret (.thunk (.lam (⟦ t ⟧ᵗ)))
  | .app t u =>
    .letin (⟦ t ⟧ᵗ)
      (.letin (renameCom succ (⟦ u ⟧ᵗ))
        (.app (.force (.var 1)) (.var 0)))
  | .inl t => .letin (⟦ t ⟧ᵗ) (.ret (.inl (.var 0)))
  | .inr t => .letin (⟦ t ⟧ᵗ) (.ret (.inr (.var 0)))
  | .case s t u =>
    .letin (⟦ s ⟧ᵗ)
      (.case (.var 0)
        (renameCom (lift succ) (⟦ t ⟧ᵗ))
        (renameCom (lift succ) (⟦ u ⟧ᵗ)))
end
local notation:40 "⟦" t:41 "⟧ᵗ" => transTerm t

/-* Translation of CBV is type preserving *-/

theorem presIn {x A Γ} (h : STLC.In x A Γ) : (⟦ Γ ⟧ᶜ) ∋ x ∶ (⟦ A ⟧ᵀ) := by
  induction h <;> constructor; assumption

theorem preservation {Γ t A} (h : Γ ⊢ₛ t ∶ A) : (⟦ Γ ⟧ᶜ) ⊢ (⟦ t ⟧ᵗ) ∶ .F (⟦ A ⟧ᵀ) := by
  induction h
  case var ih => exact .ret (.var (presIn ih))
  case unit => exact .ret .unit
  case lam ih => exact .ret (.thunk (.lam ih))
  case app iht ihu =>
    exact .letin iht
      (.letin (wtWeakenCom ihu)
        (.app (.force (.var (.there .here))) (.var .here)))
  case inl ih => exact .letin ih (.ret (.inl (.var .here)))
  case inr ih => exact .letin ih (.ret (.inr (.var .here)))
  case case ihs iht ihu =>
    exact .letin ihs (.case (.var .here) (wtWeakenCom₂ iht) (wtWeakenCom₂ ihu))

end CBV

/-*-------------------------
  Call by name translation
-------------------------*-/

namespace CBN

/-* Translation of types *-/
section
set_option hygiene false
local notation:40 "⟦" A:41 "⟧ᵀ" => transType A
def transType : STLC.SType → ComType
  | .Unit => .F .Unit
  | .Sum A₁ A₂ => .F (.Sum (.U (⟦ A₁ ⟧ᵀ)) (.U (⟦ A₂ ⟧ᵀ)))
  | .Arr A B => .Arr (.U (⟦ A ⟧ᵀ)) (⟦ B ⟧ᵀ)
end
local notation:40 "⟦" A:41 "⟧ᵀ" => transType A

/-* Translation of contexts *-/
section
set_option hygiene false
local notation:40 "⟦" Γ:41 "⟧ᶜ" => transCtxt Γ
def transCtxt : STLC.Ctxt → Ctxt
  | .nil => .nil
  | .cons Γ A => .cons (⟦ Γ ⟧ᶜ) (.U (⟦ A ⟧ᵀ))
end
local notation:40 "⟦" Γ:41 "⟧ᶜ" => transCtxt Γ

/-* Translation of terms *-/
section
set_option hygiene false
local notation:40 "⟦" t:41 "⟧ᵗ" => transTerm t
def transTerm : STLC.Term → Com
  | .var s => .force (.var s)
  | .unit => .ret .unit
  | .lam t =>.lam (⟦ t ⟧ᵗ)
  | .app t u => .app (⟦ t ⟧ᵗ) (.thunk (⟦ u ⟧ᵗ))
  | .inl t => .ret (.inl (.thunk (⟦ t ⟧ᵗ)))
  | .inr t => .ret (.inr (.thunk (⟦ t ⟧ᵗ)))
  | .case s t u =>
    .letin (⟦ s ⟧ᵗ)
      (.case (.var 0)
        (renameCom (lift succ) (⟦ t ⟧ᵗ))
        (renameCom (lift succ) (⟦ u ⟧ᵗ)))
end
local notation:40 "⟦" t:41 "⟧ᵗ" => transTerm t

/-* Translation of CBV is type preserving *-/

theorem presIn {x A Γ} (h : STLC.In x A Γ) : (⟦ Γ ⟧ᶜ) ∋ x ∶ .U (⟦ A ⟧ᵀ) := by
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

end CBN
