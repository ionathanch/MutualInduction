import CBPV.Evaluation
import CBPV.Typing

open Nat ValType ComType Val Com

/-*----------------------------------
  Logical equivalence (LE) of terms
----------------------------------*-/

mutual
@[simp]
def 𝒱 (A : ValType) (v : Val) (w : Val) : Prop :=
  match A with
  | .Unit => v = unit ∧ w = unit
  | .Sum A₁ A₂ =>
    (∃ v' w', 𝒱 A₁ v' w' ∧ v = inl v' ∧ w = inl w') ∨
    (∃ v' w', 𝒱 A₂ v' w' ∧ v = inr v' ∧ w = inr w')
  | U B => ∃ m n, ℰ B m n ∧ v = thunk m ∧ w = thunk n

@[simp]
def 𝒞 (B : ComType) (m : Com) (n : Com) : Prop :=
  match B with
  | F A => ∃ v w, 𝒱 A v w ∧ m = ret v ∧ n = ret w
  | Arr A B => ∃ m' n', (∀ v w, 𝒱 A v w → ℰ B (m'⦃v⦄) (n'⦃w⦄)) ∧
    m = lam m' ∧ n = lam n'
  | .Prod B₁ B₂ => ∃ m₁ m₂ n₁ n₂, ℰ B₁ m₁ n₁ ∧ ℰ B₂ m₂ n₂ ∧
    m = prod m₁ m₂ ∧ n = prod n₁ n₂

@[simp]
def ℰ (B : ComType) (m : Com) (n : Com) :=
  ∃ m' n', m ⇓ₙ m' ∧ n ⇓ₙ n' ∧ 𝒞 B m' n'
end

notation:40 "(" v:41 "," w:41 ")" "∈" "⟦" A:41 "⟧ᵛ" => 𝒱 A v w
notation:40 "(" m:41 "," n:41 ")" "∈" "⟦" B:41 "⟧ᶜ" => 𝒞 B m n
notation:40 "(" m:41 "," n:41 ")" "∈" "⟦" B:41 "⟧ᵉ" => ℰ B m n

/-*-------------------------------
  Convenient constructors for LE
-------------------------------*-/

theorem 𝒱.unit : 𝒱 Unit unit unit := by simp
theorem 𝒱.inl {v w A₁ A₂} (h : (v, w) ∈ ⟦A₁⟧ᵛ) : (inl v, inl w) ∈ ⟦Sum A₁ A₂⟧ᵛ := by simp [h]
theorem 𝒱.inr {v w A₁ A₂} (h : (v, w) ∈ ⟦A₂⟧ᵛ) : (inr v, inr w) ∈ ⟦Sum A₁ A₂⟧ᵛ := by simp [h]

theorem 𝒱.thunk {m n B} (h : (m, n) ∈ ⟦B⟧ᵉ) : (thunk m, thunk n) ∈ ⟦U B⟧ᵛ := by
  unfold 𝒱; exact ⟨_, _, h, rfl, rfl⟩

theorem ℰ.ret {v w A} (h : (v, w) ∈ ⟦A⟧ᵛ) : (ret v, ret w) ∈ ⟦F A⟧ᵉ := by
  unfold ℰ 𝒞; exact ⟨_, _, .refl ⟨⟩, .refl ⟨⟩, _, _, h, rfl, rfl⟩

theorem ℰ.lam {m n A B} (hB : ∀ v w, (v, w) ∈ ⟦A⟧ᵛ → (m⦃v⦄, n⦃w⦄) ∈ ⟦B⟧ᵉ) : (lam m, lam n) ∈ ⟦Arr A B⟧ᵉ := by
  unfold ℰ 𝒞; exact ⟨_, _, .refl ⟨⟩, .refl ⟨⟩, _, _, λ _ _ hA ↦ hB _ _ hA, rfl, rfl⟩

theorem ℰ.prod {m₁ m₂ n₁ n₂ B₁ B₂} (hB₁ : (m₁, n₁) ∈ ⟦B₁⟧ᵉ) (hB₂ : (m₂, n₂) ∈ ⟦B₂⟧ᵉ) : (prod m₁ m₂, prod n₁ n₂) ∈ ⟦Prod B₁ B₂⟧ᵉ:= by
  unfold ℰ 𝒞; exact ⟨_, _, .refl ⟨⟩, .refl ⟨⟩, _, _, _, _, hB₁, hB₂, rfl, rfl⟩

/-*-----------------------
  Inversion lemmas on LE
-----------------------*-/

theorem ℰ.ret_inv {m n A} (h : (m, n) ∈ ⟦F A⟧ᵉ) : ∃ v w, m ⇒⋆ .ret v ∧ n ⇒⋆ .ret w ∧ (v, w) ∈ ⟦A⟧ᵛ := by
  unfold ℰ 𝒞 at h
  let ⟨_, _, ⟨r₁, _⟩, ⟨r₂, _⟩, _, _, h, e₁, e₂⟩ := h
  subst e₁ e₂; exact ⟨_, _, r₁, r₂, h⟩

theorem ℰ.lam_inv {m₁ m₂ A B} (h : (m₁, m₂) ∈ ⟦Arr A B⟧ᵉ) : ∃ n₁ n₂, m₁ ⇒⋆ .lam n₁ ∧ m₂ ⇒⋆ .lam n₂ ∧ (∀ v w, 𝒱 A v w → ℰ B (n₁⦃v⦄) (n₂⦃w⦄)) := by
  unfold ℰ 𝒞 at h
  let ⟨_, _, ⟨r₁, _⟩, ⟨r₂, _⟩, _, _, h, e₁, e₂⟩ := h
  subst e₁ e₂; exact ⟨_, _, r₁, r₂, h⟩

theorem ℰ.fst {m n B₁ B₂} (h : (m, n) ∈ ⟦Prod B₁ B₂⟧ᵉ) : ∃ m₁ m₂ n₁ n₂, m ⇒⋆ .prod m₁ m₂ ∧ n ⇒⋆ .prod n₁ n₂ ∧ (m₁, n₁) ∈ ⟦B₁⟧ᵉ := by
  unfold ℰ 𝒞 at h
  let ⟨_, _, ⟨r₁, _⟩, ⟨r₂, _⟩, _, _, _, _, h, _, e₁, e₂⟩ := h
  subst e₁ e₂; exact ⟨_, _, _, _, r₁, r₂, h⟩

theorem ℰ.snd {m n B₁ B₂} (h : (m, n) ∈ ⟦Prod B₁ B₂⟧ᵉ) : ∃ m₁ m₂ n₁ n₂, m ⇒⋆ .prod m₁ m₂ ∧ n ⇒⋆ .prod n₁ n₂ ∧ (m₂, n₂) ∈ ⟦B₂⟧ᵉ := by
  unfold ℰ 𝒞 at h
  let ⟨_, _, ⟨r₁, _⟩, ⟨r₂, _⟩, _, _, _, _, _, h, e₁, e₂⟩ := h
  subst e₁ e₂; exact ⟨_, _, _, _, r₁, r₂, h⟩

/-*------------
  LE is a PER
------------*-/

theorem sym𝒞ℰ {B} (𝒞sym : ∀ {m n}, (m, n) ∈ ⟦B⟧ᶜ → (n, m) ∈ ⟦B⟧ᶜ) :
  ∀ {m n}, (m, n) ∈ ⟦B⟧ᵉ → (n, m) ∈ ⟦B⟧ᵉ := by
  intro _ _ h
  unfold ℰ at *
  let ⟨_, _, nm, nn, hB⟩ := h
  exact ⟨_, _, nn, nm, 𝒞sym hB⟩

theorem sym𝒱𝒞 :
  (∀ {v w A}, (v, w) ∈ ⟦A⟧ᵛ → (w, v) ∈ ⟦A⟧ᵛ) ∧
  (∀ {m n B}, (m, n) ∈ ⟦B⟧ᶜ → (n, m) ∈ ⟦B⟧ᶜ) := by
  refine ⟨λ {v w A} h ↦ ?val, λ {m n B} h ↦ ?com⟩
  mutual_induction A, B
  case Unit => unfold 𝒱 at *; simp [h]
  case Sum ihA₁ ihA₂ =>
    unfold 𝒱; unfold 𝒱 at h
    match h with
    | .inl ⟨_, _, hA₁, ev, ew⟩ => refine .inl ⟨_, _, ihA₁ hA₁, ew, ev⟩
    | .inr ⟨_, _, hA₂, ev, ew⟩ => refine .inr ⟨_, _, ihA₂ hA₂, ew, ev⟩
  case U ih =>
    unfold 𝒱 at *
    let ⟨_, _, hA, ev, ew⟩ := h
    exact ⟨_, _, sym𝒞ℰ ih hA, ew, ev⟩
  case F ih =>
    unfold 𝒞 at *
    let ⟨_, _, hB, em, en⟩ := h
    exact ⟨_, _, ih hB, en, em⟩
  case Arr ihA ihB =>
    unfold 𝒞; unfold 𝒞 at h
    let ⟨_, _, hB, em, en⟩ := h
    exact ⟨_, _, λ v w hA ↦ sym𝒞ℰ ihB (hB _ _ (ihA hA)), en, em⟩
  case Prod ihB₁ ihB₂ =>
    unfold 𝒞; unfold 𝒞 at h
    let ⟨_, _, _, _, hB₁, hB₂, em, en⟩ := h
    exact ⟨_, _, _, _, sym𝒞ℰ ihB₁ hB₁, sym𝒞ℰ ihB₂ hB₂, en, em⟩

def 𝒱.sym := @sym𝒱𝒞.left
def 𝒞.sym := @sym𝒱𝒞.right
def ℰ.sym {B} := @sym𝒞ℰ B 𝒞.sym

theorem trans𝒞ℰ {B} (𝒞trans : ∀ {m₁ m₂ m₃}, (m₁, m₂) ∈ ⟦B⟧ᶜ → (m₂, m₃) ∈ ⟦B⟧ᶜ → (m₁, m₃) ∈ ⟦B⟧ᶜ) :
  ∀ {m₁ m₂ m₃}, (m₁, m₂) ∈ ⟦B⟧ᵉ → (m₂, m₃) ∈ ⟦B⟧ᵉ → (m₁, m₃) ∈ ⟦B⟧ᵉ := by
  intro _ _ _ h₁₂ h₂₃
  unfold ℰ at *
  let ⟨m, m', nm, nm', hB₁₂⟩ := h₁₂
  let ⟨n', n, nn', nn, hB₂₃⟩ := h₂₃
  rw [Norm.join nm' nn'] at hB₁₂
  refine ⟨m, n, nm, nn, 𝒞trans hB₁₂ hB₂₃⟩

theorem trans𝒱𝒞 :
  (∀ {v₁ v₂ v₃ A}, (v₁, v₂) ∈ ⟦A⟧ᵛ → (v₂, v₃) ∈ ⟦A⟧ᵛ → (v₁, v₃) ∈ ⟦A⟧ᵛ) ∧
  (∀ {m₁ m₂ m₃ B}, (m₁, m₂) ∈ ⟦B⟧ᶜ → (m₂, m₃) ∈ ⟦B⟧ᶜ → (m₁, m₃) ∈ ⟦B⟧ᶜ) := by
  refine ⟨λ {v₁ v₂ v₃ A} h₁₂ h₂₃ ↦ ?val, λ {m₁ m₂ m₃ B} h₁₂ h₂₃ ↦ ?com⟩
  mutual_induction A, B
  case Unit =>
    unfold 𝒱 at *
    let ⟨e₁, _⟩ := h₁₂
    let ⟨_, e₃⟩ := h₂₃
    exact ⟨e₁, e₃⟩
  case Sum ihA₁ ihA₂ =>
    unfold 𝒱; unfold 𝒱 at h₁₂ h₂₃
    match h₁₂, h₂₃ with
    | .inl ⟨_, _, hA₁₂, el₁, el₂⟩, .inl ⟨_, _, hA₂₃, er₂, er₃⟩ =>
      subst el₁ el₂ er₃; injection er₂ with e; subst e
      refine .inl ⟨_, _, ihA₁ hA₁₂ hA₂₃, rfl, rfl⟩
    | .inr ⟨_, _, hA₁₂, el₁, el₂⟩, .inr ⟨_, _, hA₂₃, er₂, er₃⟩ =>
      subst el₁ el₂ er₃; injection er₂ with e; subst e
      refine .inr ⟨_, _, ihA₂ hA₁₂ hA₂₃, rfl, rfl⟩
    | .inl ⟨_, _, _, _, er⟩, .inr ⟨_, _, _, _, _⟩ => subst er; contradiction
    | .inr ⟨_, _, _, _, er⟩, .inl ⟨_, _, _, _, _⟩ => subst er; contradiction
  case U ih =>
    unfold 𝒱 at *
    let ⟨_, _, hB₁₂, el₁, el₂⟩ := h₁₂
    let ⟨_, _, hB₂₃, er₂, er₃⟩ := h₂₃
    subst el₁ el₂ er₃; injection er₂ with e; subst e
    exact ⟨_, _, trans𝒞ℰ ih hB₁₂ hB₂₃, rfl, rfl⟩
  case F ih =>
    unfold 𝒞 at *
    let ⟨_, _, hA₁₂, el₁, el₂⟩ := h₁₂
    let ⟨_, _, hA₂₃, er₂, er₃⟩ := h₂₃
    subst el₁ el₂ er₃; injection er₂ with e; subst e
    exact ⟨_, _, ih hA₁₂ hA₂₃, rfl, rfl⟩
  case Arr ihA ihB =>
    unfold 𝒞; unfold 𝒞 at h₁₂ h₂₃
    let ⟨m, m', hB₁₂, el₁, el₂⟩ := h₁₂
    let ⟨_, n, hB₂₃, er₂, er₃⟩ := h₂₃
    subst el₁ el₂ er₃; injection er₂ with e; subst e
    refine ⟨_, _, λ v w hA ↦ ?_, rfl, rfl⟩
    apply trans𝒞ℰ ihB (hB₁₂ v w hA) (hB₂₃ w w (ihA hA.sym hA))
  case Prod ihB₁ ihB₂ =>
    unfold 𝒞; unfold 𝒞 at h₁₂ h₂₃
    let ⟨_, _, _, _, hA₁₁, hA₁₂, el₁, el₂⟩ := h₁₂
    let ⟨_, _, _, _, hA₂₁, hA₂₂, er₁, er₂⟩ := h₂₃
    subst el₁ el₂ er₂; injection er₁ with e₁ e₂; subst e₁ e₂
    refine ⟨_, _, _, _, trans𝒞ℰ ihB₁ hA₁₁ hA₂₁, trans𝒞ℰ ihB₂ hA₁₂ hA₂₂, rfl, rfl⟩

def 𝒱.trans := @trans𝒱𝒞.left
def 𝒞.trans := @trans𝒱𝒞.right
def ℰ.trans {B} := @trans𝒞ℰ B 𝒞.trans

/-*-------------------------------
  Other properties of LE:
  * LE evals are backward closed
  * Reductions are LE evals
  * LE comps are normal
  * LE comps embed into evals
-------------------------------*-/

theorem ℰ.bwds {m m' n n' B} (rm : m ⇒⋆ m') (rn : n ⇒⋆ n') (h : (m', n') ∈ ⟦B⟧ᵉ) : (m, n) ∈ ⟦B⟧ᵉ := by
  unfold ℰ at *
  match h with
  | ⟨m'', n'', nm', nn', h⟩ =>
  exact ⟨m'', n'', nm'.bwd rm, nn'.bwd rn, h⟩

theorem ℰ.bwd {m m' n n' B} (rm : m ⇒ m') (rn : n ⇒ n') : (m', n') ∈ ⟦B⟧ᵉ → (m, n) ∈ ⟦B⟧ᵉ := ℰ.bwds (.once rm) (.once rn)

theorem ℰ.red {m n B} (r : m ⇒⋆ n) (h : (n, n) ∈ ⟦B⟧ᵉ) : (m, n) ∈ ⟦B⟧ᵉ := ℰ.bwds r .refl h

theorem 𝒞.nf {m n B} (h : (m, n) ∈ ⟦B⟧ᶜ) : nf m ∧ nf n := by
  match (generalizing := true) B with
  | F _ | Arr _ _ => unfold 𝒞 at h; let ⟨_, _, _, e₁, e₂⟩ := h; simp [e₁, e₂]
  | .Prod _ _ => unfold 𝒞 at h; let ⟨_, _, _, _, _, _, e₁, e₂⟩ := h; simp [e₁, e₂]

theorem 𝒞ℰ {m n A} (h : 𝒞 A m n) : ℰ A m n := by
  unfold ℰ; let ⟨nfm, nfn⟩ := h.nf; exact ⟨m, n, .refl nfm, .refl nfn, h⟩

/-*---------------------
  Semantic equivalence
---------------------*-/

/-* Semantic equivalence of contexts *-/

def semCtxt Γ (σ τ : Nat → Val) := ∀ {x A}, Γ ∋ x ∶ A → (σ x, τ x) ∈ ⟦ A ⟧ᵛ
notation:40 Γ:41 "⊨" σ:41 "~" τ:41 => semCtxt Γ σ τ

theorem semCtxtNil : ⬝ ⊨ var ~ var := by intro _ _ mem; cases mem
theorem semCtxtCons {Γ σ τ v w A} (h : (v, w) ∈ ⟦ A ⟧ᵛ) (hστ : Γ ⊨ σ ~ τ) : Γ ∷ A ⊨ v +: σ ~ w +: τ
  | _, _, .here => h
  | _, _, .there mem => hστ mem

/-* Semantic equivalence of values and computations *-/

@[reducible, simp] def semVal Γ v w A := ∀ σ τ, Γ ⊨ σ ~ τ → (v⦃σ⦄, w⦃τ⦄) ∈ ⟦ A ⟧ᵛ
@[reducible, simp] def semCom Γ m n B := ∀ σ τ, Γ ⊨ σ ~ τ → (m⦃σ⦄, n⦃τ⦄) ∈ ⟦ B ⟧ᵉ
notation:40 Γ:41 "⊨" v:41 "~" w:41 "∶" A:41 => semVal Γ v w A
notation:40 Γ:41 "⊨" m:41 "~" n:41 "∶" B:41 => semCom Γ m n B

/-* Semantic equivalence is a PER *-/

theorem symCtxtSym {Γ σ τ} (h : Γ ⊨ σ ~ τ) : Γ ⊨ τ ~ σ := λ mem ↦ (h mem).sym
theorem semValSym {Γ v w} {A : ValType} (h : Γ ⊨ v ~ w ∶ A) : Γ ⊨ w ~ v ∶ A :=
  λ _ _ hστ ↦ (h _ _ (symCtxtSym hστ)).sym
theorem semComSym {Γ m n} {B : ComType} (h : Γ ⊨ m ~ n ∶ B) : Γ ⊨ n ~ m ∶ B :=
  λ _ _ hστ ↦ (h _ _ (symCtxtSym hστ)).sym

theorem symCtxtTrans {Γ ρ σ τ} (hρσ : Γ ⊨ ρ ~ σ) (hστ : Γ ⊨ σ ~ τ) : Γ ⊨ ρ ~ τ :=
  λ mem ↦ 𝒱.trans (hρσ mem) (hστ mem)
theorem semValTrans {Γ v₁ v₂ v₃} {A : ValType} (h₁₂ : Γ ⊨ v₁ ~ v₂ ∶ A) (h₂₃ : Γ ⊨ v₂ ~ v₃ ∶ A) : Γ ⊨ v₁ ~ v₃ ∶ A :=
  λ _ _ hστ ↦ by refine 𝒱.trans (h₁₂ _ _ hστ) (h₂₃ _ _ (symCtxtTrans (symCtxtSym hστ) hστ))
theorem semComTrans {Γ m₁ m₂ m₃} {B : ComType} (h₁₂ : Γ ⊨ m₁ ~ m₂ ∶ B) (h₂₃ : Γ ⊨ m₂ ~ m₃ ∶ B) : Γ ⊨ m₁ ~ m₃ ∶ B :=
  λ _ _ hστ ↦ by refine ℰ.trans (h₁₂ _ _ hστ) (h₂₃ _ _ (symCtxtTrans (symCtxtSym hστ) hστ))

/-*---------------------------------------------
  Fundamental theorem of soundness
  of syntactic typing wrt semantic equivalence
---------------------------------------------*-/

theorem soundness {Γ} :
  (∀ (v : Val) A, Γ ⊢ v ∶ A → Γ ⊨ v ~ v ∶ A) ∧
  (∀ (m : Com) B, Γ ⊢ m ∶ B → Γ ⊨ m ~ m ∶ B) := by
  refine ⟨λ v A h ↦ ?val, λ m B h ↦ ?com⟩
  mutual_induction h, h
  all_goals intro σ τ hστ
  case var mem => exact hστ mem
  case unit => exact 𝒱.unit
  case inl ih => exact 𝒱.inl (ih σ τ hστ)
  case inr ih => exact 𝒱.inr (ih σ τ hστ)
  case thunk ih => exact 𝒱.thunk (ih σ τ hστ)
  case force ih =>
    unfold semVal 𝒱 at ih
    let ⟨_, _, h, em, en⟩ := ih σ τ hστ
    simp [-ℰ, em, en]; exact ℰ.bwd .π .π h
  case lam ih =>
    refine ℰ.lam (λ v w hA ↦ ?_)
    rw [← substUnion, ← substUnion]
    exact ih (v +: σ) (w +: τ) (semCtxtCons hA hστ)
  case app ihm ihv =>
    let ⟨_ ,_, r₁, r₂, hAB⟩ := (ihm σ τ hστ).lam_inv
    let hB := hAB _ _ (ihv σ τ hστ)
    exact ℰ.bwds (.trans' (Evals.app r₁) (.once .β)) (.trans' (Evals.app r₂) (.once .β)) hB
  case ret ih => exact ℰ.ret (ih σ τ hστ)
  case letin ihm ihn =>
    let ⟨v, w, r₁, r₂, hA⟩ := (ihm σ τ hστ).ret_inv
    refine ℰ.bwds ?_ ?_ (ihn (v +: σ) (w +: τ) (semCtxtCons hA hστ))
    all_goals rw [substUnion]
    . exact .trans' (Evals.let r₁) (.once .ζ)
    . exact .trans' (Evals.let r₂) (.once .ζ)
  case case ihv ihm ihn =>
    unfold semVal 𝒱 at ihv
    match ihv σ τ hστ with
    | .inl ⟨v, w, hA₁, ev, ew⟩ =>
      simp [-up, -ℰ, ev, ew]
      refine ℰ.bwd ?_ ?_ (ihm (v +: σ) (w +: τ) (semCtxtCons hA₁ hστ))
      all_goals rw [substUnion]; exact .ιl
    | .inr ⟨v, w, hA₂, ev, ew⟩ =>
      simp [-up, -ℰ, ev, ew]
      refine ℰ.bwd ?_ ?_ (ihn (v +: σ) (w +: τ) (semCtxtCons hA₂ hστ))
      all_goals rw [substUnion]; exact .ιr
  case prod ihm ihn => exact ℰ.prod (ihm σ τ hστ) (ihn σ τ hστ)
  case fst ih =>
    let ⟨_, _, _, _, r₁, r₂, hB₁⟩ := (ih σ τ hστ).fst
    exact ℰ.bwds (.trans' (Evals.fst r₁) (.once .π1)) (.trans' (Evals.fst r₂) (.once .π1)) hB₁
  case snd ih =>
    let ⟨_, _, _, _, r₁, r₂, hB₂⟩ := (ih σ τ hστ).snd
    exact ℰ.bwds (.trans' (Evals.snd r₁) (.once .π2)) (.trans' (Evals.snd r₂) (.once .π2)) hB₂

def soundVal {Γ v} {A : ValType} : Γ ⊢ v ∶ A → Γ ⊨ v ~ v ∶ A := soundness.left v A
def soundCom {Γ m} {B : ComType} : Γ ⊢ m ∶ B → Γ ⊨ m ~ m ∶ B := soundness.right m B

/-* ANF stuff *-/

/-* The translation continuation and plugging into a continuation *-/

inductive K : Type where
  | nil : K
  | app : Val → K → K
  | letin : Com → K
  | fst : K → K
  | snd : K → K

@[simp]
def plug (n : Com) : K → Com
  | .nil => n
  | .app v k => plug (.app n v) k
  | .letin m => .letin n m
  | .fst k => plug (.fst n) k
  | .snd k => plug (.snd n) k
notation:40 k:41 "[" n:41 "]" => plug n k

/-* Renaming continuations *-/

@[simp]
def renameK (ξ : Nat → Nat) : K → K
  | .nil => .nil
  | .app v k => .app (renameVal ξ v) (renameK ξ k)
  | .letin m => .letin (renameCom (lift ξ) m)
  | .fst k => .fst (renameK ξ k)
  | .snd k => .snd (renameK ξ k)

/-
theorem renameKExt {ξ ζ k} (h : ∀ x, ξ x = ζ x) : renameK ξ k = renameK ζ k := by
  induction k <;> simp [-lift]
  case app v _ ih => exact ⟨renameValExt _ _ h v, ih⟩
  case letin m => exact renameComExt _ _ (liftExt ξ ζ h) m
  case fst ih | snd ih => exact ih

theorem renameKComp {ξ ζ k} : (renameK ξ ∘ renameK ζ) k = renameK (ξ ∘ ζ) k := by
  induction k <;> simp [-lift]
  case app v _ ih => exact ⟨renameValComp _ _ v, ih⟩
  case letin m => exact (renameComp _ _ _ (liftComp _ _ _ (λ _ ↦ rfl))).right m
  case fst ih | snd ih => exact ih

theorem renameKLiftSucc {ξ k} : renameK succ (renameK ξ k) = renameK (lift ξ) (renameK succ k) := by
  calc renameK succ (renameK ξ k)
    _ = renameK (succ ∘ ξ) k              := renameKComp
    _ = renameK (lift ξ ∘ succ) k         := by rw [← renameKExt (liftSucc ξ)]
    _ = renameK (lift ξ) (renameK succ k) := Eq.symm renameKComp

theorem renamePlug {ξ n k} : renameCom ξ (plug n k) = plug (renameCom ξ n) (renameK ξ k) := by
  induction k generalizing ξ n <;> simp
  case app ih | fst ih | snd ih => simp [ih]
-/

/-* Substituting continuations *-/

@[simp]
def substK (σ : Nat → Val) : K → K
  | .nil => .nil
  | .app v k => .app (substVal σ v) (substK σ k)
  | .letin m => .letin (substCom (⇑ σ) m)
  | .fst k => .fst (substK σ k)
  | .snd k => .snd (substK σ k)

/-
theorem substKId {k} : substK .var k = k := by
  induction k
  case nil => rfl
  case app ih => simp [substValId _, ih]
  case letin => simp [-up, substComExt _ _ (upId _ (λ _ ↦ rfl)), substComId]
  case fst ih | snd ih => simp [ih]

theorem substKExt {σ τ k} (h : ∀ x, σ x = τ x) : substK σ k = substK τ k := by
  induction k <;> simp [-lift]
  case app v _ ih => exact ⟨substValExt _ _ h v, ih⟩
  case letin m => exact substComExt _ _ (upExt σ τ h) m
  case fst ih | snd ih => exact ih

theorem substKComp {σ τ k} : (substK σ ∘ substK τ) k = substK (substVal σ ∘ τ) k := by
  induction k <;> simp [-lift, -up]
  case app v _ ih => exact ⟨substValComp _ _ v, ih⟩
  case letin m => exact (substComp _ _ _ (upSubst _ _ _ (λ _ ↦ rfl))).right m
  case fst ih | snd ih => exact ih

theorem substRenameK {ξ σ k} : substK σ (renameK ξ k) = substK (σ ∘ ξ) k := by
  induction k <;> simp [-lift, -up]
  case app v _ ih => exact ⟨substRenameVal _ _ v, ih⟩
  case letin m => exact (substRename _ _ _ (upLift _ _ _ (λ _ ↦ rfl))).right m
  case fst ih | snd ih => exact ih

theorem renameSubstK {ξ σ k} : renameK ξ (substK σ k) = substK (renameVal ξ ∘ σ) k := by
  induction k <;> simp [-lift, -up]
  case app v _ ih => exact ⟨renameSubstVal _ _ v, ih⟩
  case letin m => exact (renameSubst _ _ _ (upRename _ _ _ (λ _ ↦ rfl))).right m
  case fst ih | snd ih => exact ih

theorem substKLiftSucc {σ k} : renameK succ (substK σ k) = substK (⇑ σ) (renameK succ k) := by
  calc renameK succ (substK σ k)
    _ = substK (renameVal succ ∘ σ) k := renameSubstK
    _ = substK (⇑ σ ∘ succ) k         := substKExt (upSucc σ)
    _ = substK (⇑ σ) (renameK succ k) := Eq.symm substRenameK
-/

theorem substPlug {σ n k} : substCom σ (plug n k) = plug (substCom σ n) (substK σ k) := by
  induction k generalizing n <;> simp
  case app ih | fst ih | snd ih => simp [ih]

/-* A-normal translation of CBPV *-/

section
set_option hygiene false
local notation:1023 "⟦" v "⟧ᵥ" => Aval v
local notation:1023 "⟦" m "⟧ₘ" => Acom .nil m
local notation:1022 "⟦" m "⟧ₘ" k => Acom k m
mutual
@[simp]
def Aval : Val → Val
  | var x => .var x
  | unit => .unit
  | inl v => .inl ⟦ v ⟧ᵥ
  | inr v => .inr ⟦ v ⟧ᵥ
  | thunk m => .thunk ⟦ m ⟧ₘ

@[simp]
def Acom (k : K) : Com → Com
  | force v => k [ .force ⟦ v ⟧ᵥ ]
  | ret v   => k [ .ret ⟦ v ⟧ᵥ ]
  | lam m   => k [ .lam ⟦ m ⟧ₘ ]
  | app n v   => ⟦ n ⟧ₘ .app ⟦ v ⟧ᵥ k
  | letin n m => ⟦ n ⟧ₘ .letin (⟦ m ⟧ₘ renameK succ k)
  | case v m₁ m₂ => .case ⟦ v ⟧ᵥ (⟦ m₁ ⟧ₘ renameK succ k) (⟦ m₂ ⟧ₘ renameK succ k)
  | prod m₁ m₂ => k [ .prod ⟦ m₁ ⟧ₘ ⟦ m₂ ⟧ₘ ]
  | fst n => ⟦ n ⟧ₘ .fst k
  | snd n => ⟦ n ⟧ₘ .snd k
  /- I think this is the A-normalization with join points?
  | case v m₁ m₂ =>
    .letin (.ret (.thunk (.com (.lam ((renameK succ k) [ .force (.var 0) ])))))
      (.case (⟦ v ⟧ᵥ)
        (.com (.app (.force (.var 1)) (.thunk (ANF.renameCfg (lift succ) (⟦ m₁ ⟧ₘ)))))
        (.com (.app (.force (.var 1)) (.thunk (ANF.renameCfg (lift succ) (⟦ m₂ ⟧ₘ))))))
  -/
end
end
notation:1023 "⟦" v "⟧ᵥ" => Aval v
notation:1023 "⟦" m "⟧ₘ" => Acom K.nil m
notation:1022 "⟦" m "⟧ₘ" k => Acom k m

/-
@[reducible, simp] def Asubst (σ : Nat → Val) : Nat → Val := λ x ↦ ⟦ σ x ⟧ᵥ
notation:1023 "⟦" σ "⟧ₛ" => Asubst σ

section
set_option hygiene false
local notation:1023 "⟦" k "⟧ₖ" => AK k
@[simp]
def AK : K → K
  | .nil => .nil
  | .app v k => .app ⟦ v ⟧ᵥ ⟦ k ⟧ₖ
  | .letin m => .letin ⟦ m ⟧ₘ
  | .fst k => .fst ⟦ k ⟧ₖ
  | .snd k => .snd ⟦ k ⟧ₖ
end
notation:1023 "⟦" k "⟧ₖ" => AK k

/-* Renaming commutes with translation *-/

theorem renameA {ξ} :
  (∀ v, ⟦ renameVal ξ v ⟧ᵥ = renameVal ξ ⟦ v ⟧ᵥ) ∧
  (∀ m k, (⟦ renameCom ξ m ⟧ₘ renameK ξ k) = renameCom ξ (⟦ m ⟧ₘ k)) := by
  refine ⟨λ v ↦ ?val, λ m k ↦ ?com⟩
  mutual_induction v, m generalizing ξ
  case var | unit => rfl
  case inl ih | inr ih => simp [ih]
  case thunk ih => simp; exact ih .nil
  case force ih | ret ih => simp [ih, renamePlug]
  case lam ih =>
    have e := ih (ξ := lift ξ) .nil
    simp [-lift] at *; rw [e]; simp [renamePlug]
  case app ihm ihv => simp [-lift, ihv, ← ihm]
  case letin ihn ihm =>
    simp [-lift, ← ihn, ← ihm, renameKLiftSucc]
  case case ihv ihm₁ ihm₂ =>
    simp [-lift, ihv, ← ihm₁, ← ihm₂, renameKLiftSucc]
  case prod ihm₁ ihm₂ => simp [← ihm₁, ← ihm₂, renamePlug]
  case fst ih | snd ih => simp [← ih]

theorem renameAval {ξ v} : ⟦ renameVal ξ v ⟧ᵥ = renameVal ξ ⟦ v ⟧ᵥ := renameA.left v
theorem renameAcom {ξ m k} : (⟦ renameCom ξ m ⟧ₘ renameK ξ k) = renameCom ξ (⟦ m ⟧ₘ k) := renameA.right m k

/-* Substitution commutes with translation *-/

theorem substAupCom {σ m} : substCom ⟦ ⇑ σ ⟧ₛ m = substCom (⇑ ⟦ σ ⟧ₛ) m := by
  apply substComExt; intro n; cases n <;> simp [renameAval]

theorem substAupK {σ k} : substK ⟦ ⇑ σ ⟧ₛ k = substK (⇑ ⟦ σ ⟧ₛ) k := by
  apply substKExt; intro n; cases n <;> simp [renameAval]

theorem substA {σ} :
  (∀ v, ⟦ substVal σ v ⟧ᵥ = substVal ⟦ σ ⟧ₛ ⟦ v ⟧ᵥ) ∧
  (∀ m k, (⟦ substCom σ m ⟧ₘ substK ⟦ σ ⟧ₛ k) = substCom ⟦ σ ⟧ₛ (⟦ m ⟧ₘ k)) := by
  refine ⟨λ v ↦ ?val, λ m k ↦ ?com⟩
  mutual_induction v, m generalizing σ
  case var | unit => rfl
  case inl ih | inr ih => simp [ih]
  case thunk ih => simp; exact ih .nil
  case force ih | ret ih => simp [ih, substPlug]
  case lam ih =>
    have e := ih (σ := ⇑ σ) .nil
    simp [-lift, -up] at *; rw [e]; simp [-up, substPlug, substAupCom]
  case app ihm ihv => simp [-up, ← ihv, ← ihm]
  case letin ihn ihm =>
    simp [-lift, -up, ← ihn, ← substAupCom, ← ihm, substKLiftSucc, substAupK]
  case case ihv ihm₁ ihm₂ =>
    have eσ {σ} : (.var 0 +: renameVal succ ∘ σ) = ⇑ σ := rfl
    simp [-lift, -up, ihv, substKLiftSucc, ← substAupCom, ← substAupK, ihm₁, ihm₂]
  case prod ihm₁ ihm₂ => simp [← ihm₁, ← ihm₂, substPlug]
  case fst ih | snd ih => simp [← ih]

theorem substAval {σ v} : ⟦ substVal σ v ⟧ᵥ = substVal ⟦ σ ⟧ₛ ⟦ v ⟧ᵥ := substA.left v
theorem substAcom {σ m k} : (⟦ substCom σ m ⟧ₘ substK ⟦ σ ⟧ₛ k) = substCom ⟦ σ ⟧ₛ (⟦ m ⟧ₘ k) := substA.right m k

theorem substAcomOne {m : Com} {v : Val} {k} : substCom (⟦ v ⟧ᵥ +: .var) (⟦ m ⟧ₘ renameK succ k) = (⟦ m⦃v⦄ ⟧ₘ k) := by
  calc substCom (⟦ v ⟧ᵥ +: .var) (⟦ m ⟧ₘ renameK succ k)
    _ = substCom (⟦ v +: .var ⟧ₛ) (⟦ m ⟧ₘ renameK succ k)  := by rw [substComExt _ _ (λ n ↦ ?_)]; cases n <;> simp
    _ = ⟦ m⦃v⦄ ⟧ₘ (substK ⟦ v +: .var ⟧ₛ (renameK succ k)) := Eq.symm substAcom
    _ = ⟦ m⦃v⦄ ⟧ₘ (substK (⟦ v +: .var ⟧ₛ ∘ succ) k)       := by rw [substRenameK]
    _ = ⟦ m⦃v⦄ ⟧ₘ (substK .var k)                          := by rw [substKExt (λ n ↦ ?_)]; cases n <;> simp
    _ = ⟦ m⦃v⦄ ⟧ₘ k                                        := by rw [substKId]

-/

/-* Typing continuations *-/

section
set_option hygiene false
open K
local notation:40 Γ:41 "⊢" k:41 "∶" B₁:41 "⇒" B₂:41 => KWt Γ k B₁ B₂
inductive KWt : Ctxt → K → ComType → ComType → Prop where
  | nil {Γ B} :
    ---------------
    Γ ⊢ nil ∶ B ⇒ B
  | app {Γ k v B₁ B₂} {A : ValType} :
    Γ ⊢ v ∶ A →
    Γ ⊢ k ∶ B₁ ⇒ B₂ →
    -----------------------------
    Γ ⊢ app v k ∶ (Arr A B₁) ⇒ B₂
  | letin {Γ m A} {B : ComType} :
    Γ ∷ A ⊢ m ∶ B →
    ---------------------
    Γ ⊢ letin m ∶ F A ⇒ B
  | fst {Γ k B₁ B₂ B₃} :
    Γ ⊢ k ∶ B₁ ⇒ B₃ →
    -----------------------------
    Γ ⊢ fst k ∶ (Prod B₁ B₂) ⇒ B₃
  | snd {Γ k B₁ B₂ B₃} :
    Γ ⊢ k ∶ B₂ ⇒ B₃ →
    -----------------------------
    Γ ⊢ snd k ∶ (Prod B₁ B₂) ⇒ B₃
end
notation:40 Γ:41 "⊢" k:41 "∶" B₁:41 "⇒" B₂:41 => KWt Γ k B₁ B₂

theorem wtRenameK {ξ k B₁ B₂} {Γ Δ : Ctxt} (hξ : Δ ⊢ ξ ∶ Γ) (h : Γ ⊢ k ∶ B₁ ⇒ B₂) :
  Δ ⊢ renameK ξ k ∶ B₁ ⇒ B₂ := by
  induction h generalizing ξ Δ
  all_goals constructor <;> apply_rules [wtRenameVal, wtRenameCom, wRenameLift]

theorem wtWeakenK {Γ k A B₁ B₂} : Γ ⊢ k ∶ B₁ ⇒ B₂ → Γ ∷ A ⊢ renameK succ k ∶ B₁ ⇒ B₂ :=
  wtRenameK wRenameSucc

theorem wtPlug {Γ n k B₁ B₂}
  (hk : Γ ⊢ k ∶ B₁ ⇒ B₂) (h : Γ ⊢ n ∶ B₁) : Γ ⊢ (k [ n ]) ∶ B₂ := by
  induction hk generalizing n
  case nil => exact h
  case app hv _ hn => exact hn (.app h hv)
  case letin hm => exact .letin h hm
  case fst hn => exact hn (.fst h)
  case snd hn => exact hn (.snd h)

/-* Semantic equivalence of continuations *-/

section
set_option hygiene false
local notation:40 "(" k₁:41 "," k₂:41 ")" "∈" "⟦" B₁:41 "⇒" B₂:41 "⟧ᵏ'" => 𝒦' B₁ B₂ k₁ k₂
local notation:40 "(" k₁:41 "," k₂:41 ")" "∈" "⟦" B₁:41 "⇒" B₂:41 "⟧ᵏ" => 𝒦 B₁ B₂ k₁ k₂
mutual
@[simp]
def 𝒦' (B₁ B₂ : ComType) (k₁ k₂ : K) : Prop :=
  match B₁ with
  | F A => ∃ m n, (∀ v w, (v, w) ∈ ⟦A⟧ᵛ → (m⦃v⦄, n⦃w⦄) ∈ ⟦B₂⟧ᵉ) ∧
    k₁ = .letin m ∧ k₂ = .letin n
  | Arr A B => ∃ v w k₁' k₂', (v, w) ∈ ⟦A⟧ᵛ ∧ (k₁', k₂') ∈ ⟦B ⇒ B₂⟧ᵏ ∧
    k₁ = .app v k₁' ∧ k₂ = .app w k₂'
  | .Prod B₀ B₁ =>
    (∃ k₁' k₂', (k₁', k₂') ∈ ⟦B₀ ⇒ B₂⟧ᵏ ∧ k₁ = .fst k₁' ∧ k₂ = .fst k₂') ∨
    (∃ k₁' k₂', (k₁', k₂') ∈ ⟦B₁ ⇒ B₂⟧ᵏ ∧ k₁ = .snd k₁' ∧ k₂ = .snd k₂')

@[simp]
def 𝒦 (B₁ B₂ : ComType) (k₁ k₂ : K) : Prop :=
  (B₁ = B₂ ∧ k₁ = .nil ∧ k₂ = .nil) ∨ (k₁, k₂) ∈ ⟦B₁ ⇒ B₂⟧ᵏ'
end
end

notation:40 "(" k₁:41 "," k₂:41 ")" "∈" "⟦" B₁:41 "⇒" B₂:41 "⟧ᵏ'" => 𝒦' B₁ B₂ k₁ k₂
notation:40 "(" k₁:41 "," k₂:41 ")" "∈" "⟦" B₁:41 "⇒" B₂:41 "⟧ᵏ" => 𝒦 B₁ B₂ k₁ k₂

def 𝒦.nil {B} : (.nil, .nil) ∈ ⟦B ⇒ B⟧ᵏ := by simp
def 𝒦.letin {m n A B} (h : ∀ v w, (v, w) ∈ ⟦A⟧ᵛ → (m⦃v⦄, n⦃w⦄) ∈ ⟦B⟧ᵉ) : (.letin m, .letin n) ∈ ⟦F A ⇒ B⟧ᵏ := by
  unfold 𝒦 𝒦'; exact .inr ⟨_, _, h, rfl, rfl⟩
def 𝒦.app {v w k₁ k₂ A B₁ B₂} (hA : (v, w) ∈ ⟦A⟧ᵛ) (h : (k₁, k₂) ∈ ⟦B₁ ⇒ B₂⟧ᵏ) : (.app v k₁, .app w k₂) ∈ ⟦Arr A B₁ ⇒ B₂⟧ᵏ := by
  unfold 𝒦 𝒦'; exact .inr ⟨_, _, _ ,_, hA, h, rfl, rfl⟩
def 𝒦.fst {k₁ k₂ B₁ B₂ B₃} (h : (k₁, k₂) ∈ ⟦B₁ ⇒ B₃⟧ᵏ) : (.fst k₁, .fst k₂) ∈ ⟦Prod B₁ B₂ ⇒ B₃⟧ᵏ := by
  unfold 𝒦 𝒦'; exact .inr (.inl ⟨_, _, h, rfl, rfl⟩)
def 𝒦.snd {k₁ k₂ B₁ B₂ B₃} (h : (k₁, k₂) ∈ ⟦B₂ ⇒ B₃⟧ᵏ) : (.snd k₁, .snd k₂) ∈ ⟦Prod B₁ B₂ ⇒ B₃⟧ᵏ := by
  unfold 𝒦 𝒦'; exact .inr (.inr ⟨_, _, h, rfl, rfl⟩)

@[reducible, simp] def semK Γ k₁ k₂ B₁ B₂ := ∀ σ τ, Γ ⊨ σ ~ τ → (substK σ k₁, substK τ k₂) ∈ ⟦B₁ ⇒ B₂⟧ᵏ
notation:40 Γ:41 "⊨" k₁:41 "~" k₂:41 "∶" B₁:41 "⇒" B₂:41 => semK Γ k₁ k₂ B₁ B₂

theorem soundK {Γ k B₁ B₂} (h : Γ ⊢ k ∶ B₁ ⇒ B₂) : Γ ⊨ k ~ k ∶ B₁ ⇒ B₂ := by
  induction h <;> intro σ τ hστ
  case nil => exact .nil
  case app hv _ ih => exact .app (soundVal hv σ τ hστ) (ih σ τ hστ)
  case letin hm =>
    refine .letin (λ v w hA ↦ ?_)
    rw [← substUnion, ← substUnion]
    refine soundCom hm (v +: σ) (w +: τ) (semCtxtCons hA hστ)
  case fst ih => exact .fst (ih σ τ hστ)
  case snd ih => exact .snd (ih σ τ hστ)

/-* Semantic proofs *-/

theorem semPlug {Γ n₁ n₂ k B₁ B₂} (h : Γ ⊢ k ∶ B₁ ⇒ B₂) (hn : Γ ⊨ n₁ ~ n₂ ∶ B₁) : Γ ⊨ (k [ n₁ ]) ~ (k [ n₂ ]) ∶ B₂ := by
  induction h generalizing n₁ n₂
  case nil => exact hn
  case app hv _ ih =>
    apply ih; intro σ τ hστ
    let ⟨_ ,_, r₁, r₂, hAB⟩ := (hn σ τ hστ).lam_inv
    let hB := hAB _ _ (soundVal hv σ τ hστ)
    exact ℰ.bwds (.trans' (Evals.app r₁) (.once .β)) (.trans' (Evals.app r₂) (.once .β)) hB
  case letin hm =>
    intro σ τ hστ
    let ⟨v, w, r₁, r₂, hA⟩ := (hn σ τ hστ).ret_inv
    refine ℰ.bwds ?_ ?_ (soundCom hm (v +: σ) (w +: τ) (semCtxtCons hA hστ))
    all_goals rw [substUnion]
    . exact .trans' (Evals.let r₁) (.once .ζ)
    . exact .trans' (Evals.let r₂) (.once .ζ)
  case fst ih =>
    apply ih; intro σ τ hστ
    let ⟨_, _, _, _, r₁, r₂, hB₁⟩ := (hn σ τ hστ).fst
    exact ℰ.bwds (.trans' (Evals.fst r₁) (.once .π1)) (.trans' (Evals.fst r₂) (.once .π1)) hB₁
  case snd ih =>
    apply ih; intro σ τ hστ
    let ⟨_, _, _, _, r₁, r₂, hB₂⟩ := (hn σ τ hστ).snd
    exact ℰ.bwds (.trans' (Evals.snd r₁) (.once .π2)) (.trans' (Evals.snd r₂) (.once .π2)) hB₂

theorem semPlugg {Γ n₁ n₂ k₁ k₂ B₁ B₂} (hk : Γ ⊨ k₁ ~ k₂ ∶ B₁ ⇒ B₂) (hn : Γ ⊨ n₁ ~ n₂ ∶ B₁) : Γ ⊨ (k₁[n₁]) ~ (k₂[n₂]) ∶ B₂ := by
  mutual_induction B₁ generalizing Γ B₂ hn <;> intro σ τ hστ
  case F =>
    specialize hk σ τ hστ
    unfold 𝒦 at hk
    match hk with
    | .inl ⟨eB, ek₁, ek₂⟩ => subst eB; rw [substPlug, substPlug, ek₁, ek₂]; exact hn σ τ hστ
    | .inr hk =>
      unfold 𝒦' at hk
      let ⟨v, w, rv, rw, hA⟩ := (hn σ τ hστ).ret_inv
      let ⟨m, n, hB₂, ek₁, ek₂⟩ := hk
      specialize hB₂ v w hA
      rw [substPlug, substPlug, ek₁, ek₂]
      refine ℰ.bwds ?_ ?_ hB₂
      . exact .trans' (Evals.let rv) (.once .ζ)
      . exact .trans' (Evals.let rw) (.once .ζ)
  case Arr ih =>
    specialize hk σ τ hστ
    unfold 𝒦 at hk
    match hk with
    | .inl ⟨eB, ek₁, ek₂⟩ => subst eB; rw [substPlug, substPlug, ek₁, ek₂]; exact hn σ τ hστ
    | .inr hk =>
      unfold 𝒦' at hk
      let ⟨v, w, k₁, k₂, hA, hB, ek₁, ek₂⟩ := hk
      rw [substPlug, substPlug, ek₁, ek₂]
      unfold 𝒦 at hB
      match hB with
      | .inl ⟨eB₂, ek₁, ek₂⟩ =>
        subst eB₂; rw [ek₁, ek₂]; unfold plug
        sorry -- usual application case
      | .inr hk => sorry
  sorry

theorem semKletin {Γ n m k B₁ B₂} (hk : Γ ⊢ k ∶ B₁ ⇒ B₂) (h : Γ ⊢ letin n m ∶ B₁) :
  Γ ⊨ (k [letin n m]) ~ letin n ((renameK succ k) [m]) ∶ B₂ := by
  induction hk generalizing n m
  case nil => exact soundCom h
  case app hk ih =>
    apply semComTrans (semPlug hk ?_) (ih ?_)
    sorry; sorry -- app commutes with case
  case letin hm =>
    simp [-semCom, -lift]
    sorry -- let commutes with let
  case fst hk ih =>
    apply semComTrans (semPlug hk ?_) (ih ?_)
    sorry; sorry -- fst commutes with let
  case snd hk ih =>
    apply semComTrans (semPlug hk ?_) (ih ?_)
    sorry; sorry -- snd commutes with let

theorem semKcase {Γ v m₁ m₂ k B₁ B₂} (hk : Γ ⊢ k ∶ B₁ ⇒ B₂) (h : Γ ⊢ case v m₁ m₂ ∶ B₁) :
  Γ ⊨ (k [case v m₁ m₂]) ~ case v ((renameK succ k) [m₁]) ((renameK succ k) [m₂]) ∶ B₂ := by
  induction hk generalizing v m₁ m₂
  case nil => exact soundCom h
  case app hk ih =>
    apply semComTrans (semPlug hk ?_) (ih ?_)
    sorry; sorry -- app commutes with case
  case letin hm =>
    simp [-semCom, -lift]
    sorry -- let commutes with case
  case fst hk ih =>
    apply semComTrans (semPlug hk ?_) (ih ?_)
    sorry; sorry -- fst commutes with case
  case snd hk ih =>
    apply semComTrans (semPlug hk ?_) (ih ?_)
    sorry; sorry -- snd commutes with case

theorem what {Γ} :
  (∀ v (A : ValType), Γ ⊢ v ∶ A → Γ ⊨ v ~ ⟦v⟧ᵥ ∶ A) ∧
  (∀ m k (B₁ B₂ : ComType), Γ ⊢ m ∶ B₁ → Γ ⊢ k ∶ B₁ ⇒ B₂ → Γ ⊨ (k[m]) ~ ⟦m⟧ₘ k ∶ B₂) := by
  refine ⟨λ v A h ↦ ?val, λ m k B₁ B₂ h hk ↦ ?com⟩
  mutual_induction h, h
  case app m v _ _ _ _  ihn ihv =>
    have e : (k [app m v]) = ((K.app v k) [m]) := by rfl
    unfold Acom; rw [e]; sorry
  case letin m _ _ hn hm ihn ihm =>
    refine semComTrans (semKletin hk (.letin hn hm)) ?_
    intro σ τ hστ
    specialize ihn _ _ (.letin (m := (renameK succ k) [m]) (wtPlug (wtWeakenK hk) hm))
    specialize ihm _ _ (wtWeakenK hk)
    simp only [Acom]; simp only [plug] at ihn; sorry
  case case hv hm₁ hm₂ ihv ihm₁ ihm₂ =>
    refine semComTrans (semKcase hk (.case hv hm₁ hm₂)) ?_
    intro σ τ hστ
    unfold semVal 𝒱 at ihv
    match ihv σ τ hστ with
    | .inl ⟨v, w, hA₁, ev, ew⟩ =>
      simp [-up, -ℰ, ev, ew]
      refine ℰ.bwd ?_ ?_ (ihm₁ _ _ (wtWeakenK hk) (v +: σ) (w +: τ) (semCtxtCons hA₁ hστ))
      all_goals rw [substUnion]; exact .ιl
    | .inr ⟨v, w, hA₂, ev, ew⟩ =>
      simp [-up, -ℰ, ev, ew]
      refine ℰ.bwd ?_ ?_ (ihm₂ _ _ (wtWeakenK hk) (v +: σ) (w +: τ) (semCtxtCons hA₂ hστ))
      all_goals rw [substUnion]; exact .ιr
  all_goals intro σ τ hστ
  case var mem => exact hστ mem
  case unit => exact 𝒱.unit
  case inl ih => exact 𝒱.inl (ih σ τ hστ)
  case inr ih => exact 𝒱.inr (ih σ τ hστ)
  case thunk ih => exact 𝒱.thunk (ih .nil _ .nil σ τ hστ)
  case force ih =>
    refine semPlug hk (λ σ τ hστ ↦ ?_) σ τ hστ
    unfold semVal 𝒱 at ih
    let ⟨_, _, h, em, en⟩ := ih σ τ hστ
    simp [-ℰ, em, en]; exact ℰ.bwd .π .π h
  case lam B _ ih =>
    refine semPlug hk (λ σ τ hστ ↦ ?_) σ τ hστ
    refine ℰ.lam (λ v w hA ↦ ?_)
    rw [← substUnion, ← substUnion]
    refine ih .nil B .nil (v +: σ) (w +: τ) (semCtxtCons hA hστ)
  case ret ih =>
    refine semPlug hk (λ σ τ hστ ↦ ?_) σ τ hστ
    exact ℰ.ret (ih σ τ hστ)
  case prod ihn₁ ihn₂ =>
    refine semPlug hk (λ σ τ hστ ↦ ?_) σ τ hστ
    exact ℰ.prod (ihn₁ .nil _ .nil σ τ hστ) (ihn₂ .nil _ .nil σ τ hστ)
  case fst ih => exact ih (.fst k) _ (.fst hk) σ τ hστ
  case snd ih => exact ih (.snd k) _ (.snd hk) σ τ hστ
