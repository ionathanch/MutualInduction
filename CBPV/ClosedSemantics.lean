import CBPV.Reduction
import CBPV.Typing

open ValType ComType Val Com

/-*--------------------------
  Logical relation on types
--------------------------*-/

mutual
@[simp]
def 𝒱 (A : ValType) (v : Val) : Prop :=
  match A with
  | .Unit => v = unit
  | U B => ∃ m, ℰ B m ∧ v = thunk m

@[simp]
def 𝒞 (B : ComType) (m : Com) : Prop :=
  match B with
  | F A => ∃ v, 𝒱 A v ∧ m = ret v
  | Arr A₁ A₂ => ∃ n, (∀ v, 𝒱 A₁ v → ℰ A₂ (n⦃v⦄)) ∧ m = lam n

@[simp]
def ℰ (B : ComType) (m : Com) := ∃ n, m ⇓ n ∧ 𝒞 B n
end
notation:40 v:41 "∈" "⟦" A:41 "⟧ᵛ" => 𝒱 A v
notation:40 m:41 "∈" "⟦" B:41 "⟧ᶜ" => 𝒞 B m
notation:40 m:41 "∈" "⟦" B:41 "⟧ᵉ" => ℰ B m

-- Convenient constructors for the logical relation
theorem 𝒱.unit : 𝒱 Unit unit := by simp
theorem 𝒱.thunk {m B} (h : ℰ B m) : 𝒱 (U B) (thunk m) := by simp at *; assumption
theorem 𝒞.ret {v A} (h : 𝒱 A v) : 𝒞 (F A) (ret v) := by simp; assumption
theorem 𝒞.lam {n A₁ A₂} (h : ∀ v, 𝒱 A₁ v → ℰ A₂ (n⦃v⦄)) : 𝒞 (Arr A₁ A₂) (lam n) := by simp at *; assumption

-- Semantic computations are normal
theorem 𝒞nf {B m} (h : m ∈ ⟦ B ⟧ᶜ) : nf m :=
  match (generalizing := true) B with
  | F _ | Arr _ _ =>
    by simp at h; let ⟨_, _, e⟩ := h; subst e; exact ⟨⟩

-- Semantic computations embed into semantic evaluations
theorem 𝒞ℰ {B m} (h : m ∈ ⟦ B ⟧ᶜ) : m ∈ ⟦ B ⟧ᵉ :=
  by simp; exact ⟨m, ⟨.refl m, 𝒞nf h⟩, h⟩

-- Semantic evaluations are backward closed under reduction
theorem ℰbwd {B m n} (r : m ⇒⋆ n) (h : n ∈ ⟦ B ⟧ᵉ) : m ∈ ⟦ B ⟧ᵉ := by
  unfold ℰ at *
  let ⟨n', ⟨r', nfn⟩, h⟩ := h
  refine ⟨n', ⟨trans' r r', nfn⟩, h⟩
theorem 𝒞bwd {B m n} (r : m ⇒⋆ n) (h : n ∈ ⟦ B ⟧ᶜ) : m ∈ ⟦ B ⟧ᵉ := ℰbwd r (𝒞ℰ h)

/-*----------------
  Semantic typing
----------------*-/

-- Semantic well-formedness of contexts
def semCtxt Γ (σ : Nat → Val) := ∀ {x A}, Γ ∋ x ∶ A → σ x ∈ ⟦ A ⟧ᵛ
notation:40 Γ:41 "⊨" σ:41 => semCtxt Γ σ

-- Convenient constructors for semantic contexts
theorem semCtxtNil : ⬝ ⊨ var := by intro _ _ mem; cases mem
theorem semCtxtCons {Γ σ v A} (h : v ∈ ⟦ A ⟧ᵛ) (hσ : Γ ⊨ σ) : Γ ∷ A ⊨ v +: σ
  | _, _, .here => h
  | _, _, .there mem => hσ mem

-- Semantic typing of values and computations
@[simp] def semVal Γ v A := ∀ σ, Γ ⊨ σ → v⦃σ⦄ ∈ ⟦ A ⟧ᵛ
@[simp] def semCom Γ m B := ∀ σ, Γ ⊨ σ → m⦃σ⦄ ∈ ⟦ B ⟧ᵉ
notation:40 Γ:41 "⊨" v:41 "∶" A:41 => semVal Γ v A
notation:40 Γ:41 "⊨" m:41 "∶" B:41 => semCom Γ m B

/-*----------------------------------------
  Fundamental theorem of soundness
  of syntactic typing wrt semantic typing
----------------------------------------*-/

theorem soundness {Γ} :
  (∀ (v : Val) A, Γ ⊢ v ∶ A → Γ ⊨ v ∶ A) ∧
  (∀ (m : Com) B, Γ ⊢ m ∶ B → Γ ⊨ m ∶ B) := by
  refine ⟨λ v A h ↦ ?val, λ m B h ↦ ?com⟩
  mutual_induction h, h
  all_goals intro σ hσ
  case var mem => exact hσ mem
  case unit => exact 𝒱.unit
  case thunk ih => exact 𝒱.thunk (ih σ hσ)
  case force ih =>
    simp at ih
    let ⟨_, ⟨_, ⟨r, _⟩, h⟩, e⟩ := ih σ hσ
    let rf := Steps.trans .force r
    rw [← e] at rf
    exact 𝒞bwd rf h
  case lam ih =>
    apply 𝒞ℰ; apply 𝒞.lam
    intro v hv; rw [← substUnion]
    exact ih (v +: σ) (semCtxtCons hv hσ)
  case app ihm ihv =>
    simp at ihm
    let ⟨_, ⟨rlam, _⟩, _, h, e⟩ := ihm σ hσ; subst e
    let ⟨_, ⟨rval, _⟩, h⟩ := h _ (ihv σ hσ)
    exact 𝒞bwd (trans' (stepsApp rlam) (.trans .lam rval)) h
  case ret ih => exact 𝒞ℰ (𝒞.ret (ih σ hσ))
  case letin ihret ih =>
    simp at ihret ih
    let ⟨_, ⟨rret, _⟩, v, hv, e⟩ := ihret σ hσ; subst e
    let ⟨_, ⟨rlet, nflet⟩, h⟩ := ih (v +: σ) (semCtxtCons hv hσ)
    rw [substUnion] at rlet
    exact 𝒞bwd (trans' (stepsLet rret) (.trans .ret rlet)) h

-- If a computation does not step, then it is in normal form
theorem normal {m B} (nr : ∀ {n}, ¬ m ⇒ n) (h : ⬝ ⊢ m ∶ B) : nf m := by
  let ⟨_, soundCom⟩ := soundness (Γ := ⬝)
  let mB := soundCom m B h
  simp at mB
  let ⟨_, ⟨r, nfm⟩, _⟩ := mB var semCtxtNil
  rw [substComId] at r
  cases r with | refl => exact nfm | trans r _ => cases nr r

-- Computations are strongly normalizing
theorem normalization {m : Com} {B : ComType} (h : ⬝ ⊢ m ∶ B) : SN m := by
  let ⟨_, soundCom⟩ := soundness (Γ := ⬝)
  let mB := soundCom m B h
  simp at mB
  let ⟨_, ⟨r, nfm⟩, _⟩ := mB var semCtxtNil
  rw [substComId] at r
  exact stepsSN r nfm
