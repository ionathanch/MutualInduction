import CBPV.Evaluation
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
  | .Sum A₁ A₂ => (∃ w, 𝒱 A₁ w ∧ v = inl w) ∨ (∃ w, 𝒱 A₂ w ∧ v = inr w)
  | U B => ∃ m, ℰ B m ∧ v = thunk m

@[simp]
def 𝒞 (B : ComType) (m : Com) : Prop :=
  match B with
  | F A => ∃ v, 𝒱 A v ∧ m = ret v
  | Arr A B => ∃ n, (∀ v, 𝒱 A v → ℰ B (n⦃v⦄)) ∧ m = lam n
  | .Prod B₁ B₂ => ∃ n₁ n₂, ℰ B₁ n₁ ∧ ℰ B₂ n₂ ∧ m = prod n₁ n₂

@[simp]
def ℰ (B : ComType) (m : Com) := ∃ n, m ⇓ n ∧ 𝒞 B n
end
notation:40 v:41 "∈" "⟦" A:41 "⟧ᵛ" => 𝒱 A v
notation:40 m:41 "∈" "⟦" B:41 "⟧ᶜ" => 𝒞 B m
notation:40 m:41 "∈" "⟦" B:41 "⟧ᵉ" => ℰ B m

-- Convenient constructors for the logical relation
theorem 𝒱.unit : 𝒱 Unit unit := by simp
theorem 𝒱.inl {v A₁ A₂} (h : 𝒱 A₁ v) : 𝒱 (Sum A₁ A₂) (inl v) := by simp; assumption
theorem 𝒱.inr {v A₁ A₂} (h : 𝒱 A₂ v) : 𝒱 (Sum A₁ A₂) (inr v) := by simp; assumption
theorem 𝒱.thunk {m B} (h : ℰ B m) : 𝒱 (U B) (thunk m) := by simp at *; assumption
theorem 𝒞.ret {v A} (h : 𝒱 A v) : 𝒞 (F A) (ret v) := by simp; assumption
theorem 𝒞.lam {n A B} (h : ∀ v, 𝒱 A v → ℰ B (n⦃v⦄)) : 𝒞 (Arr A B) (lam n) := by simp at *; assumption
theorem 𝒞.prod {m n B₁ B₂} (hm : ℰ B₁ m) (hn : ℰ B₂ n) : 𝒞 (Prod B₁ B₂) (prod m n) := by simp at *; constructor <;> assumption

-- Semantic computations are normal
theorem 𝒞nf {B m} (h : m ∈ ⟦ B ⟧ᶜ) : nf m :=
  match (generalizing := true) B with
  | F _ | Arr _ _ =>
    by simp at h; let ⟨_, _, e⟩ := h; subst e; exact ⟨⟩
  | .Prod _ _ =>
    by simp at h; let ⟨_, _, _, _, e⟩ := h; subst e; exact ⟨⟩

-- Semantic computations embed into semantic evaluations
theorem 𝒞ℰ {B m} (h : m ∈ ⟦ B ⟧ᶜ) : m ∈ ⟦ B ⟧ᵉ :=
  by simp; exact ⟨m, ⟨.refl, 𝒞nf h⟩, h⟩

-- Semantic evaluations are backward closed under reduction
theorem ℰbwd {B m n} (r : m ⇒⋆ n) (h : n ∈ ⟦ B ⟧ᵉ) : m ∈ ⟦ B ⟧ᵉ := by
  unfold ℰ at *
  let ⟨n', ⟨r', nfn⟩, h⟩ := h
  refine ⟨n', ⟨.trans' r r', nfn⟩, h⟩
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
@[reducible, simp] def semVal Γ v A := ∀ σ, Γ ⊨ σ → v⦃σ⦄ ∈ ⟦ A ⟧ᵛ
@[reducible, simp] def semCom Γ m B := ∀ σ, Γ ⊨ σ → m⦃σ⦄ ∈ ⟦ B ⟧ᵉ
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
  case inl ih => exact 𝒱.inl (ih σ hσ)
  case inr ih => exact 𝒱.inr (ih σ hσ)
  case thunk ih => exact 𝒱.thunk (ih σ hσ)
  case force ih =>
    simp at ih
    let ⟨_, ⟨_, ⟨r, _⟩, h⟩, e⟩ := ih σ hσ
    let rf : _ ⇒⋆ _ := .trans .force r
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
    exact 𝒞bwd (Trans.trans (Evals.app rlam) (Trans.trans Eval.lam rval)) h
  case ret ih => exact 𝒞ℰ (𝒞.ret (ih σ hσ))
  case letin ihret ih =>
    simp at ihret ih
    let ⟨_, ⟨rret, _⟩, v, hv, e⟩ := ihret σ hσ; subst e
    let ⟨_, ⟨rlet, nflet⟩, h⟩ := ih (v +: σ) (semCtxtCons hv hσ)
    rw [substUnion] at rlet
    exact 𝒞bwd (Trans.trans (Evals.let rret) (Trans.trans Eval.ret rlet)) h
  case case m n _ _ _ _ _ _ ihv ihm ihn =>
    simp at ihv
    match ihv σ hσ with
    | .inl ⟨v, hv, e⟩ =>
      let hm := ihm (v +: σ) (semCtxtCons hv hσ)
      simp only [substCom]; rw [e]; rw [substUnion] at hm
      exact ℰbwd (.once .inl) hm
    | .inr ⟨v, hv, e⟩ =>
      let hn := ihn (v +: σ) (semCtxtCons hv hσ)
      simp only [substCom]; rw [e]; rw [substUnion] at hn
      exact ℰbwd (.once .inr) hn
  case prod m n _ _ _ _ ihm ihn =>
    simp at ihm ihn
    let ⟨_, ⟨rm, _⟩, hm⟩ := ihm σ hσ
    let ⟨_, ⟨rn, _⟩, hn⟩ := ihn σ hσ
    apply 𝒞ℰ; exact 𝒞.prod (𝒞bwd rm hm) (𝒞bwd rn hn)
  case prjl ih =>
    simp [-𝒞] at ih; unfold 𝒞 at ih
    let ⟨_, ⟨rprod, nfprod⟩, n₁, n₂, hm, _, e⟩ := ih σ hσ; subst e
    let r : prjl (_⦃σ⦄) ⇒⋆ n₁ := Trans.trans (Evals.prjl rprod) Eval.prodl
    exact ℰbwd r hm
  case prjr ih =>
    simp [-𝒞] at ih; unfold 𝒞 at ih
    let ⟨_, ⟨rprod, nfprod⟩, n₁, n₂, _, hn, e⟩ := ih σ hσ; subst e
    let r : prjr (_⦃σ⦄) ⇒⋆ n₂ := Trans.trans (Evals.prjr rprod) Eval.prodr
    exact ℰbwd r hn

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
  exact r.sn nfm
