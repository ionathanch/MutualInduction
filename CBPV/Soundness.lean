import CBPV.OpenSemantics
import CBPV.Typing

open ValType ComType Val Com

/-*----------------
  Semantic typing
----------------*-/

-- Semantic well-formedness of contexts
def semCtxt Γ (σ : Nat → Val) := ∀ {x A}, Γ ∋ x ∶ A → ∀ {P}, ⟦ A ⟧ᵛ ↘ P → P (σ x)
notation:40 Γ:41 "⊨" σ:41 => semCtxt Γ σ

-- Convenient constructors for semantic contexts
theorem semCtxtVar {Γ} : Γ ⊨ var :=  λ _ _ hA ↦ hA.sneVal .var
theorem semCtxtNil : ⬝ ⊨ var := semCtxtVar
theorem semCtxtCons {Γ σ v A P} (h : ⟦ A ⟧ᵛ ↘ P) (pv : P v) (hσ : Γ ⊨ σ) : Γ ∷ A ⊨ v +: σ
  | _, _, .here, _, h' => by rw [𝒱.det h' h]; exact pv
  | _, _, .there mem, _, h => hσ mem h

-- Semantic typing of values and computations
@[simp] def semVal Γ v A := ∀ σ, Γ ⊨ σ → ∃ P, ⟦ A ⟧ᵛ ↘ P ∧ P (v⦃σ⦄)
@[simp] def semCom Γ m B := ∀ σ, Γ ⊨ σ → ∃ P, ⟦ B ⟧ᶜ ↘ P ∧ P (m⦃σ⦄)
notation:40 Γ:41 "⊨" v:41 "∶" A:41 => semVal Γ v A
notation:40 Γ:41 "⊨" m:41 "∶" B:41 => semCom Γ m B

/-*------------------------------
  Fundamental soundness theorem
------------------------------*-/

theorem SNup {Γ σ A B P} {m : Com}
  (hσ : Γ ⊨ σ) (hA : ⟦ A ⟧ᵛ ↘ P) (h : Γ ∷ A ⊨ m ∶ B) : SNCom (m⦃⇑ σ⦄) := by
  let ⟨Q, hB, qm⟩ := h (var 0 +: σ) (semCtxtCons hA (hA.sneVal .var) hσ)
  rw [substComVar] at qm
  exact (hB.snCom qm).antirenaming

theorem soundness {Γ} :
  (∀ (v : Val) A, Γ ⊢ v ∶ A → Γ ⊨ v ∶ A) ∧
  (∀ (m : Com) B, Γ ⊢ m ∶ B → Γ ⊨ m ∶ B) := by
  refine ⟨λ v A h ↦ ?val, λ m B h ↦ ?com⟩
  mutual_induction h, h
  all_goals intro σ hσ
  case var A mem =>
    let ⟨P, hA⟩ := A.interp
    exact ⟨P, hA, hσ mem hA⟩
  case unit => exact ⟨_, .Unit, .inr .refl⟩
  case inl A₂ _ ih =>
    let ⟨_, hA₂⟩ := A₂.interp
    let ⟨_, hA₁, pv⟩ := ih σ hσ
    refine ⟨_, .Sum hA₁ hA₂, .inr (.inl ⟨_, .refl, pv⟩)⟩
  case inr A₁ _ _ ih =>
    let ⟨_, hA₁⟩ := A₁.interp
    let ⟨_, hA₂, pv⟩ := ih σ hσ
    refine ⟨_, .Sum hA₁ hA₂, .inr (.inr ⟨_, .refl, pv⟩)⟩
  case thunk ih =>
    let ⟨_, hB, pm⟩ := ih σ hσ
    exact ⟨_, .U hB, hB.closure (.once .thunk) pm⟩
  case force ih =>
    let ⟨_, hUB, pv⟩ := ih σ hσ
    cases hUB with | U hB => exact ⟨_, hB, pv⟩
  case lam m A B _ ih =>
    let ⟨P, hA⟩ := A.interp
    let ⟨Q, hB⟩ := B.interp
    refine ⟨_, .Arr hA hB, λ v pv ↦ ?_⟩
    let ⟨_, hB', pm⟩ := ih (v +: σ) (semCtxtCons hA pv hσ)
    rw [𝒞.det hB' hB] at pm
    let r : app ((lam m)⦃σ⦄) v ⤳⋆ m⦃v +: σ⦄ := by
      calc
        app ((lam m)⦃σ⦄) v
        _ ⤳⋆ app (lam (m⦃⇑ σ⦄)) v := .refl
        _ ⤳⋆ m⦃⇑ σ⦄⦃v⦄            := .once (.lam (hA.snVal pv))
        _ ⤳⋆ m⦃v +: σ⦄            := by rw [← substUnion]
    exact hB.closure r pm
  case app ihm ihv =>
    let ⟨_, hArr, pm⟩ := ihm σ hσ
    let ⟨_, hA, pv⟩ := ihv σ hσ
    cases hArr with | Arr hA' hB =>
      rw [𝒱.det hA hA'] at pv
      exact ⟨_, hB, pm _ pv⟩
  case ret ih =>
    let ⟨_, hA, pv⟩ := ih σ hσ
    exact ⟨_, .F hA, Or.inr ⟨_, .refl, pv⟩⟩
  case letin m n _ B _ _ ihm ihn =>
    let ⟨_, hFA, pm⟩ := ihm σ hσ
    cases hFA with | F hA =>
    match pm with
    | .inl ⟨_, r, sne⟩ =>
      let ⟨P, hB⟩ := B.interp
      let plet := hB.sneCom (.letin sne (SNup hσ hA ihn))
      exact ⟨P, hB, hB.closure (.letin r) plet⟩
    | .inr ⟨v, r, pv⟩ =>
      let ⟨_, hB, pn⟩ := ihn (v +: σ) (semCtxtCons hA pv hσ)
      let r' : (letin m n)⦃σ⦄ ⤳⋆ n⦃v +: σ⦄ := by
        calc
          (letin m n)⦃σ⦄
          _ ⤳⋆ letin (m⦃σ⦄) (n⦃⇑ σ⦄)   := .refl
          _ ⤳⋆ letin (.ret v) (n⦃⇑ σ⦄) := .letin r
          _ ⤳⋆ n⦃⇑ σ⦄⦃v⦄               := .once (.ret (hA.snVal pv))
          _ ⤳⋆ n⦃v +: σ⦄               := by rw [← substUnion]
      exact ⟨_, hB, hB.closure r' pn⟩
  case case v m n _ _ B _ _ _ ihv ihm ihn =>
    let ⟨_, hSum, pv⟩ := ihv σ hσ
    cases hSum with | Sum hA₁ hA₂ =>
      let snm := SNup hσ hA₁ ihm
      let snn := SNup hσ hA₂ ihn
      match pv with
      | .inl sne =>
        let ⟨P, hB⟩ := B.interp
        exact ⟨P, hB, hB.sneCom (.case sne snm snn)⟩
      | .inr (.inl ⟨w, r, pv⟩) =>
        let ⟨R, hB, rm⟩ := ihm (w +: σ) (semCtxtCons hA₁ pv hσ)
        let r' : (case v m n)⦃σ⦄ ⤳⋆ m⦃w +: σ⦄ := by
          calc
            (case v m n)⦃σ⦄
            _ ⤳⋆ case (v⦃σ⦄) (m⦃⇑ σ⦄) (n⦃⇑ σ⦄) := .refl
            _ ⤳⋆ case (inl w) (m⦃⇑ σ⦄) (n⦃⇑ σ⦄) := .case r
            _ ⤳⋆ m⦃⇑ σ⦄⦃w⦄                      := .once (.inl snn)
            _ ⤳⋆ m⦃w +: σ⦄                      := by rw [← substUnion]
        exact ⟨R, hB, hB.closure r' rm⟩
      | .inr (.inr ⟨w, r, qv⟩) =>
        let ⟨R, hB, rm⟩ := ihn (w +: σ) (semCtxtCons hA₂ qv hσ)
        let r' : (case v m n)⦃σ⦄ ⤳⋆ n⦃w +: σ⦄ := by
          calc
            (case v m n)⦃σ⦄
            _ ⤳⋆ case (v⦃σ⦄) (m⦃⇑ σ⦄) (n⦃⇑ σ⦄) := .refl
            _ ⤳⋆ case (inr w) (m⦃⇑ σ⦄) (n⦃⇑ σ⦄) := .case r
            _ ⤳⋆ n⦃⇑ σ⦄⦃w⦄                      := .once (.inr snm)
            _ ⤳⋆ n⦃w +: σ⦄                      := by rw [← substUnion]
        exact ⟨R, hB, hB.closure r' rm⟩

theorem normalization {Γ} :
  (∀ {v : Val} {A}, Γ ⊢ v ∶ A → SNVal v) ∧
  (∀ {m : Com} {B}, Γ ⊢ m ∶ B → SNCom m) := by
  let ⟨soundVal, soundCom⟩ := @soundness Γ
  refine ⟨λ h ↦ ?val, λ h ↦ ?com⟩
  case val =>
    let ⟨_, hA, pv⟩ := soundVal _ _ h _ semCtxtVar
    rw [substValId] at pv
    exact hA.snVal pv
  case com =>
    let ⟨_, hB, pm⟩ := soundCom _ _ h _ semCtxtVar
    rw [substComId] at pm
    exact hB.snCom pm
