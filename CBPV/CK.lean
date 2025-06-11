import CBPV.Syntax

inductive F : Type where
  | app : Val → F
  | letin : Com → F

def K := List F
def CK := Com × K

section
set_option hygiene false
local infix:40 "⤳" => Step
inductive Step : CK → CK → Prop where
  | β {m v k} :     ⟨.lam m, .app v :: k⟩   ⤳ ⟨substCom (v +: .var) m, k⟩
  | ιl {v m n k} :  ⟨.case (.inl v) m n, k⟩ ⤳ ⟨substCom (v +: .var) m, k⟩
  | ιr {v m n k} :  ⟨.case (.inr v) m n, k⟩ ⤳ ⟨substCom (v +: .var) n, k⟩
  | π {m k} :       ⟨.force (.thunk m), k⟩  ⤳ ⟨m, k⟩
  | ζ {v m k} :     ⟨.ret v, .letin m :: k⟩ ⤳ ⟨substCom (v +: .var) m, k⟩
  | app {m v k} :   ⟨.app m v, k⟩           ⤳ ⟨m, .app v :: k⟩
  | letin {m n k} : ⟨.letin m n, k⟩         ⤳ ⟨m, .letin n :: k⟩
end
infix:40 "⤳" => Step

/-* Reflexive, transitive closure *-/

inductive RTC {A : Type} (R : A → A → Prop) : A → A → Prop
  | refl {a} : RTC R a a
  | trans {a b c} : R a b → RTC R b c → RTC R a c
infix:40 "⤳⋆"  => RTC Step

def RTC.trans' {A R} {a b c : A} (rab : RTC R a b) (rbc : RTC R b c) : RTC R a c := by
  induction rab
  case refl => exact rbc
  case trans => constructor <;> apply_rules

def RTC.once {A R} {a b : A} (r : R a b) : RTC R a b := .trans r .refl

instance {A} {R : A → A → Prop} : Trans R (RTC R) (RTC R) where
  trans := .trans

instance {A} {R : A → A → Prop} : Trans R R (RTC R) where
  trans r₁ r₂ := .trans r₁ (.once r₂)

instance {A} {R : A → A → Prop} : Trans (RTC R) R (RTC R) where
  trans r₁ r₂ := .trans' r₁ (.once r₂)
