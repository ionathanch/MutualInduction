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
  | π {m} : force (thunk m) ⇒ m
  | β {m v} : app (lam m) v ⇒ m⦃v⦄
  | ζ {v m} : letin (ret v) m ⇒ m⦃v⦄
  | ιl {v m n} : case (inl v) m n ⇒ m⦃v⦄
  | ιr {v m n} : case (inr v) m n ⇒ n⦃v⦄
  | π1 {m n} : fst (prod m n) ⇒ m
  | π2 {m n} : snd (prod m n) ⇒ n
  | app {m m' v} :
    m ⇒ m' →
    ------------------
    app m v ⇒ app m' v
  | letin {m m' n} :
    m ⇒ m' →
    ----------------------
    letin m n ⇒ letin m' n
  | fst {m m'} :
    m ⇒ m' →
    ----------------
    fst m ⇒ fst m'
  | snd {m m'} :
    m ⇒ m' →
    ----------------
    snd m ⇒ snd m'
end
infix:40 "⇒" => Eval

-- Single-step evaluation is deterministic
theorem evalDet {m n₁ n₂} (r₁ : m ⇒ n₁) (r₂ : m ⇒ n₂) : n₁ = n₂ := by
  induction r₁ generalizing n₂
  all_goals cases r₂; try rfl
  case fst.fst ih _ r | snd.snd ih _ r => rw [ih r]
  all_goals try apply_rules [appCong, letinCong, prodCong]
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

theorem Evals.fst {m m'} (r : m ⇒⋆ m') : fst m ⇒⋆ fst m' := by
  induction r
  case refl => exact .refl
  case trans r _ ih => exact .trans (.fst r) ih

theorem Evals.snd {m m'} (r : m ⇒⋆ m') : snd m ⇒⋆ snd m' := by
  induction r
  case refl => exact .refl
  case trans r _ ih => exact .trans (.snd r) ih

theorem Evals.ret_inv {v m} (r : ret v ⇒⋆ m) : ret v = m := by
  generalize e : ret v = n at r
  induction r generalizing v <;> subst e
  case refl => rfl
  case trans r => cases r

theorem Evals.lam_inv {m n} (r : lam m ⇒⋆ n) : lam m = n := by
  generalize e : lam m = m' at r
  induction r generalizing m <;> subst e
  case refl => rfl
  case trans r => cases r

theorem Evals.prod_inv {m₁ m₂ n} (r : prod m₁ m₂ ⇒⋆ n) : prod m₁ m₂ = n := by
  generalize e : prod m₁ m₂ = m at r
  induction r generalizing m₁ m₂ <;> subst e
  case refl => rfl
  case trans r => cases r

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
  | lam _ | ret _ | prod _ _ => True
  | force _ | app _ _ | letin _ _ | case _ _ _ | fst _ | snd _ => False

theorem nfStepn't {m n} (nfm : nf m) : ¬ m ⇒ n := by
  cases m <;> simp at *
  all_goals intro r; cases r

theorem nfSteps {m n} (nfm : nf m) (r : m ⇒⋆ n) : m = n := by
  cases r
  case refl => rfl
  case trans r _ => cases nfStepn't nfm r

@[reducible] def Norm (m n : Com) := m ⇒⋆ n ∧ nf n
infix:40 "⇓ₙ" => Norm

@[refl] theorem Norm.refl {m} (nfm : nf m) : m ⇓ₙ m := by exists .refl

theorem Norm.bwd {m m' n} (r : m ⇒⋆ m') : m' ⇓ₙ n → m ⇓ₙ n
  | ⟨rn, nfn⟩ => ⟨.trans' r rn, nfn⟩

theorem Norm.join {m n₁ n₂} : m ⇓ₙ n₁ → m ⇓ₙ n₂ → n₁ = n₂
  | ⟨rn₁, nfn₁⟩, ⟨rn₂, nfn₂⟩ =>
    let ⟨n', rn₁', rn₂'⟩ := confluence rn₁ rn₂
    by rw [nfSteps nfn₁ rn₁', nfSteps nfn₂ rn₂']

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
