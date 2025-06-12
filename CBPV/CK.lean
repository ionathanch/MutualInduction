import CBPV.RTC
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

@[reducible] def Steps := RTC Step
infix:40 "⤳⋆"  => Steps
