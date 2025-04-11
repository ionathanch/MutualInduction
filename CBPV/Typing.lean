import CBPV.Syntax

open ValType ComType Val Com

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
end
end

notation:40 Γ:41 "⊢" v:41 "∶" A:41 => ValWt Γ v A
notation:40 Γ:41 "⊢" m:41 "∶" B:41 => ComWt Γ m B
