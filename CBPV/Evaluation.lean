import CBPV.RTC
import CBPV.Syntax

open Val Com

/-*-----------------------
  Single-step evaluation
-----------------------*-/

section
set_option hygiene false
local infix:40 "⇒" => Eval
inductive Eval : Com → Com → Prop where
  | force {m} : force (thunk m) ⇒ m
  | lam {m v} : app (lam m) v ⇒ m⦃v⦄
  | ret {v m} : letin (ret v) m ⇒ m⦃v⦄
  | inl {v m n} : case (inl v) m n ⇒ m⦃v⦄
  | inr {v m n} : case (inr v) m n ⇒ n⦃v⦄
  | app {m m' v} :
    m ⇒ m' →
    ------------------
    app m v ⇒ app m' v
  | letin {m m' n} :
    m ⇒ m' →
    ----------------------
    letin m n ⇒ letin m' n
end
infix:40 "⇒" => Eval

-- Single-step evaluation is deterministic
theorem evalDet {m n₁ n₂} (r₁ : m ⇒ n₁) (r₂ : m ⇒ n₂) : n₁ = n₂ := by
  induction r₁ generalizing n₂
  all_goals cases r₂; try rfl
  all_goals apply_rules [appCong, letinCong]
  all_goals rename _ ⇒ _ => r; cases r

/-*----------------------
  Multi-step evaluation
----------------------*-/

@[reducible] def Evals := RTC Eval
infix:40 "⇒⋆" => Evals

theorem Evals.app {m n v} (r : m ⇒⋆ n) : app m v ⇒⋆ app n v := by
  induction r
  case refl => exact .refl
  case trans r _ ih => exact .trans (.app r) ih

theorem Evals.let {m m' n} (r : m ⇒⋆ m') : letin m n ⇒⋆ letin m' n := by
  induction r
  case refl => exact .refl
  case trans r _ ih => exact .trans (.letin r) ih

-- Multi-step reduction is confluent trivially by determinism
theorem confluence {m n₁ n₂} (r₁ : m ⇒⋆ n₁) (r₂ : m ⇒⋆ n₂) : ∃ m', n₁ ⇒⋆ m' ∧ n₂ ⇒⋆ m' := by
  induction r₁ generalizing n₂
  case refl => exact ⟨n₂, r₂, .refl⟩
  case trans r₁ rs₁ ih =>
    cases r₂
    case refl => exact ⟨_, .refl, .trans r₁ rs₁⟩
    case trans r₂ rs₂ => rw [evalDet r₁ r₂] at *; exact ih rs₂

/-*----------------------------
  Normal forms and evaluation
----------------------------*-/

@[simp]
def nf : Com → Prop
  | lam _ | ret _ => True
  | force _ | .app _ _ | letin _ _ | case _ _ _ => False

theorem nfStepn't {m n} (nfm : nf m) : ¬ m ⇒ n := by
  cases m <;> simp at *
  all_goals intro r; cases r

def Norm (m n : Com) := m ⇒⋆ n ∧ nf n
infix:40 "⇓" => Norm

/-*---------------------
  Strong normalization
---------------------*-/

inductive SN : Com → Prop where
  | sn : ∀ m, (∀ n, m ⇒ n → SN n) → SN m

theorem SN.nf {m} (nfm : nf m) : SN m := by
  constructor; intro n r; cases nfStepn't nfm r

theorem Evals.sn {m n} (r : m ⇒⋆ n) (nfn : nf n) : SN m := by
  induction r
  case refl => exact .nf nfn
  case trans r _ ih => constructor; intro _ r'; rw [← evalDet r r']; exact ih nfn
