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

theorem SNup {Γ σ A B} {m : Com}
  (hσ : Γ ⊨ σ) (h : Γ ∷ A ⊨ m ∶ B) : SNCom (m⦃⇑ σ⦄) := by
  let ⟨P, hA⟩ := A.interp
  let ⟨Q, hB, qm⟩ := h (var 0 +: σ) (semCtxtCons hA (hA.sneVal .var) hσ)
  rw [substVar] at qm
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
  case unit => exact ⟨_, .Unit, .inr rfl⟩
  case inl A₂ _ ih =>
    let ⟨_, hA₂⟩ := A₂.interp
    let ⟨_, hA₁, pv⟩ := ih σ hσ
    exact ⟨_, .Sum hA₁ hA₂, .inr (.inl ⟨_, rfl, pv⟩)⟩
  case inr A₁ _ _ ih =>
    let ⟨_, hA₁⟩ := A₁.interp
    let ⟨_, hA₂, pv⟩ := ih σ hσ
    exact ⟨_, .Sum hA₁ hA₂, .inr (.inr ⟨_, rfl, pv⟩)⟩
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
    let r : app ((lam m)⦃σ⦄) v ⤳ m⦃v +: σ⦄ := by
      calc app ((lam m)⦃σ⦄) v
        _ = app (lam (m⦃⇑ σ⦄)) v := rfl
        _ ⤳ m⦃⇑ σ⦄⦃v⦄            := .lam (hA.snVal pv)
        _ = (m⦃v +: σ⦄)          := by rw [← substUnion]
    exact hB.closure (.once r) pm
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
      let plet := hB.sneCom (.letin sne (SNup hσ ihn))
      exact ⟨P, hB, hB.closure (.letin r) plet⟩
    | .inr ⟨v, r, pv⟩ =>
      let ⟨_, hB, pn⟩ := ihn (v +: σ) (semCtxtCons hA pv hσ)
      let r' : (letin m n)⦃σ⦄ ⤳⋆ n⦃v +: σ⦄ := by
        calc (letin m n)⦃σ⦄
          _ = letin (m⦃σ⦄) (n⦃⇑ σ⦄)    := rfl
          _ ⤳⋆ letin (.ret v) (n⦃⇑ σ⦄) := .letin r
          _ ⤳ n⦃⇑ σ⦄⦃v⦄                := .ret (hA.snVal pv)
          _ = (n⦃v +: σ⦄)              := by rw [← substUnion]
      exact ⟨_, hB, hB.closure r' pn⟩
  case case v m n _ _ B _ _ _ ihv ihm ihn =>
    let ⟨_, hSum, pv⟩ := ihv σ hσ
    cases hSum with | Sum hA₁ hA₂ =>
    let snm := SNup hσ ihm
    let snn := SNup hσ ihn
    match pv with
    | .inl sne =>
      let ⟨P, hB⟩ := B.interp
      exact ⟨P, hB, hB.sneCom (.case sne snm snn)⟩
    | .inr (.inl ⟨w, e, pv⟩) =>
      let snv := hA₁.snVal pv
      let ⟨R, hB, rm⟩ := ihm (w +: σ) (semCtxtCons hA₁ pv hσ)
      simp only [substCom]
      let r : (case v m n)⦃σ⦄ ⤳ m⦃w +: σ⦄ := by
        calc (case v m n)⦃σ⦄
          _ = (case (inl w) (m⦃⇑ σ⦄) (n⦃⇑ σ⦄)) := by simp only [substCom]; rw [e]
          _ ⤳ m⦃⇑ σ⦄⦃w⦄                        := .inl snv snn
          _ = (m⦃w +: σ⦄)                      := by rw [← substUnion]
      exact ⟨R, hB, hB.closure (.once r) rm⟩
    | .inr (.inr ⟨w, e, qv⟩) =>
      let snv := hA₂.snVal qv
      let ⟨R, hB, rm⟩ := ihn (w +: σ) (semCtxtCons hA₂ qv hσ)
      let r' : (case v m n)⦃σ⦄ ⤳ n⦃w +: σ⦄ := by
        calc (case v m n)⦃σ⦄
          _ = case (inr w) (m⦃⇑ σ⦄) (n⦃⇑ σ⦄) := by simp only [substCom]; rw [e]
          _ ⤳ n⦃⇑ σ⦄⦃w⦄                      := .inr snv snm
          _ = (n⦃w +: σ⦄)                    := by rw [← substUnion]
      exact ⟨R, hB, hB.closure (.once r') rm⟩
  case prod ihm ihn =>
    let ⟨_, hB₁, pm⟩ := ihm σ hσ
    let ⟨_, hB₂, pn⟩ := ihn σ hσ
    exact ⟨_, .Prod hB₁ hB₂, .inr ⟨_, _, .refl, pm, pn⟩⟩
  case prjl m _ _ _ ihm =>
    let ⟨_, hProd, pm⟩ := ihm σ hσ
    cases hProd with | Prod hB₁ hB₂ =>
    match pm with
    | .inl ⟨_, r, sne⟩ => exact ⟨_, hB₁, hB₁.closure (.prjl r) (hB₁.sneCom (.prjl sne))⟩
    | .inr ⟨n₁, n₂, r, pn₁, pn₂⟩ =>
      let r' : prjl (m⦃σ⦄) ⤳⋆ n₁ := by
        calc prjl (m⦃σ⦄)
          _ ⤳⋆ prjl (prod n₁ n₂) := .prjl r
          _ ⤳⋆ n₁                := .once (.prodl (hB₂.snCom pn₂))
      refine ⟨_, hB₁, hB₁.closure r' pn₁⟩
  case prjr m _ _ _ ihm =>
    let ⟨_, hProd, pm⟩ := ihm σ hσ
    cases hProd with | Prod hB₁ hB₂ =>
    match pm with
    | .inl ⟨_, r, sne⟩ => exact ⟨_, hB₂, hB₂.closure (.prjr r) (hB₂.sneCom (.prjr sne))⟩
    | .inr ⟨n₁, n₂, r, pn₁, pn₂⟩ =>
      let r' : prjr (m⦃σ⦄) ⤳⋆ n₂ := by
        calc prjr (m⦃σ⦄)
          _ ⤳⋆ prjr (prod n₁ n₂) := .prjr r
          _ ⤳⋆ n₂                := .once (.prodr (hB₁.snCom pn₁))
      refine ⟨_, hB₂, hB₂.closure r' pn₂⟩
