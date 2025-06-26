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

theorem semCtxt.nil : ⬝ ⊨ var ~ var := by intro _ _ mem; cases mem
theorem semCtxt.cons {Γ σ τ v w A} (h : (v, w) ∈ ⟦ A ⟧ᵛ) (hστ : Γ ⊨ σ ~ τ) : Γ ∷ A ⊨ v +: σ ~ w +: τ
  | _, _, .here => h
  | _, _, .there mem => hστ mem

theorem semCtxt.rename {ξ σ τ} {Γ Δ : Ctxt} (hξ : Γ ⊢ ξ ∶ Δ) (h : Γ ⊨ σ ~ τ) : Δ ⊨ σ ∘ ξ ~ τ ∘ ξ :=
  λ mem ↦ h (hξ _ _  mem)

/-* Semantic equivalence of values and computations *-/

@[reducible, simp] def semVal Γ v w A := ∀ σ τ, Γ ⊨ σ ~ τ → (v⦃σ⦄, w⦃τ⦄) ∈ ⟦ A ⟧ᵛ
@[reducible, simp] def semCom Γ m n B := ∀ σ τ, Γ ⊨ σ ~ τ → (m⦃σ⦄, n⦃τ⦄) ∈ ⟦ B ⟧ᵉ
notation:40 Γ:41 "⊨" v:41 "~" w:41 "∶" A:41 => semVal Γ v w A
notation:40 Γ:41 "⊨" m:41 "~" n:41 "∶" B:41 => semCom Γ m n B

/-* Semantic equivalence is a PER *-/

theorem semCtxt.sym {Γ σ τ} (h : Γ ⊨ σ ~ τ) : Γ ⊨ τ ~ σ := λ mem ↦ (h mem).sym
theorem semVal.sym {Γ v w} {A : ValType} (h : Γ ⊨ v ~ w ∶ A) : Γ ⊨ w ~ v ∶ A :=
  λ _ _ hστ ↦ (h _ _ hστ.sym).sym
theorem semCom.sym {Γ m n} {B : ComType} (h : Γ ⊨ m ~ n ∶ B) : Γ ⊨ n ~ m ∶ B :=
  λ _ _ hστ ↦ (h _ _ hστ.sym).sym

theorem semCtxt.trans {Γ ρ σ τ} (hρσ : Γ ⊨ ρ ~ σ) (hστ : Γ ⊨ σ ~ τ) : Γ ⊨ ρ ~ τ :=
  λ mem ↦ 𝒱.trans (hρσ mem) (hστ mem)
theorem semVal.trans {Γ v₁ v₂ v₃} {A : ValType} (h₁₂ : Γ ⊨ v₁ ~ v₂ ∶ A) (h₂₃ : Γ ⊨ v₂ ~ v₃ ∶ A) : Γ ⊨ v₁ ~ v₃ ∶ A :=
  λ _ _ hστ ↦ by refine 𝒱.trans (h₁₂ _ _ hστ) (h₂₃ _ _ (semCtxt.trans hστ.sym hστ))
theorem semCom.trans {Γ m₁ m₂ m₃} {B : ComType} (h₁₂ : Γ ⊨ m₁ ~ m₂ ∶ B) (h₂₃ : Γ ⊨ m₂ ~ m₃ ∶ B) : Γ ⊨ m₁ ~ m₃ ∶ B :=
  λ _ _ hστ ↦ by refine ℰ.trans (h₁₂ _ _ hστ) (h₂₃ _ _ (semCtxt.trans hστ.sym hστ))

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
    exact ih (v +: σ) (w +: τ) (semCtxt.cons hA hστ)
  case app ihm ihv =>
    let ⟨_ ,_, r₁, r₂, hAB⟩ := (ihm σ τ hστ).lam_inv
    let hB := hAB _ _ (ihv σ τ hστ)
    exact ℰ.bwds (.trans' (Evals.app r₁) (.once .β)) (.trans' (Evals.app r₂) (.once .β)) hB
  case ret ih => exact ℰ.ret (ih σ τ hστ)
  case letin ihm ihn =>
    let ⟨v, w, r₁, r₂, hA⟩ := (ihm σ τ hστ).ret_inv
    refine ℰ.bwds ?_ ?_ (ihn (v +: σ) (w +: τ) (semCtxt.cons hA hστ))
    all_goals rw [substUnion]
    . exact .trans' (Evals.let r₁) (.once .ζ)
    . exact .trans' (Evals.let r₂) (.once .ζ)
  case case ihv ihm ihn =>
    unfold semVal 𝒱 at ihv
    match ihv σ τ hστ with
    | .inl ⟨v, w, hA₁, ev, ew⟩ =>
      simp [-up, -ℰ, ev, ew]
      refine ℰ.bwd ?_ ?_ (ihm (v +: σ) (w +: τ) (semCtxt.cons hA₁ hστ))
      all_goals rw [substUnion]; exact .ιl
    | .inr ⟨v, w, hA₂, ev, ew⟩ =>
      simp [-up, -ℰ, ev, ew]
      refine ℰ.bwd ?_ ?_ (ihn (v +: σ) (w +: τ) (semCtxt.cons hA₂ hστ))
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

/-*-------------------------------
  Various commuting equivalences
-------------------------------*-/

theorem appCase {Γ v w m₁ m₂ A B}
  (hcase : Γ ⊢ case v m₁ m₂ ∶ Arr A B)
  (hw : Γ ⊢ w ∶ A) :
  Γ ⊨ app (case v m₁ m₂) w ~ case v (app m₁ (renameVal succ w)) (app m₂ (renameVal succ w)) ∶ B := by
  intro σ τ hστ
  let ⟨n₁, n₂, r₁, r₂, hB₁⟩ := (soundCom hcase σ τ hστ).lam_inv
  have r₁' : app (case v m₁ m₂⦃σ⦄) (w⦃σ⦄) ⇒⋆ n₁⦃w⦃σ⦄⦄ := .trans' r₁.app (.once .β)
  simp only [substCom] at *
  cases hcase with case case hv hm₁ hm₂ =>
  let hv := soundVal hv σ τ hστ; unfold 𝒱 at hv
  match hv with
  | .inl ⟨v₁, v₂, hA₁, e₁, e₂⟩ =>
    let ⟨_, _, _, r₂', hB₂⟩ := (soundCom hm₁ (v₁ +: σ) (v₂ +: τ) (semCtxt.cons hA₁ hστ)).lam_inv
    rw [e₂]; rw [e₂] at r₂
    let ⟨_, rlam₁, r'⟩ := confluence r₂ (.once .ιl); rw [← substUnion] at r'
    let ⟨_, rlam₂, r'⟩ := confluence r₂' r'; rw [← rlam₂.lam_inv] at r'
    injection Evals.lam_inv (.trans' rlam₁ r') with en₂; subst en₂
    have r₂' :
      case (.inl v₂) (app (m₁⦃⇑ τ⦄) (renameVal succ w⦃⇑ τ⦄)) (app (m₂⦃⇑ τ⦄) (renameVal succ w⦃⇑ τ⦄))
        ⇒⋆ n₂⦃w⦃τ⦄⦄ := calc
      _ ⇒⋆ app (m₁⦃⇑ τ⦄) (renameVal succ w⦃⇑ τ⦄) ⦃v₂⦄ := .once .ιl
      _ =  app (m₁⦃v₂ +: τ⦄) (w⦃τ⦄)                    := by simp only [substCom]; rw [← substUnion, ← renameUpSubstVal, ← substDropVal]
      _ ⇒⋆ app (lam n₂) (w⦃τ⦄)                         := r₂'.app
      _ ⇒  n₂⦃w⦃τ⦄⦄                                    := .β
    exact ℰ.bwds r₁' r₂' (hB₁ _ _ (soundVal hw σ τ hστ))
  | .inr ⟨v₁, v₂, hA₁, e₁, e₂⟩ =>
    let ⟨_, _, _, r₂', hB₂⟩ := (soundCom hm₂ (v₁ +: σ) (v₂ +: τ) (semCtxt.cons hA₁ hστ)).lam_inv
    rw [e₂]; rw [e₂] at r₂
    let ⟨_, rlam₁, r'⟩ := confluence r₂ (.once .ιr); rw [← substUnion] at r'
    let ⟨_, rlam₂, r'⟩ := confluence r₂' r'; rw [← rlam₂.lam_inv] at r'
    injection Evals.lam_inv (.trans' rlam₁ r') with en₂; subst en₂
    have r₂' :
      case (.inr v₂) (app (m₁⦃⇑ τ⦄) (renameVal succ w⦃⇑ τ⦄)) (app (m₂⦃⇑ τ⦄) (renameVal succ w⦃⇑ τ⦄))
        ⇒⋆ n₂⦃w⦃τ⦄⦄ := calc
      _ ⇒⋆ app (m₂⦃⇑ τ⦄) (renameVal succ w⦃⇑ τ⦄) ⦃v₂⦄ := .once .ιr
      _ =  app (m₂⦃v₂ +: τ⦄) (w⦃τ⦄)                    := by simp only [substCom]; rw [← substUnion, ← renameUpSubstVal, ← substDropVal]
      _ ⇒⋆ app (lam n₂) (w⦃τ⦄)                         := r₂'.app
      _ ⇒  n₂⦃w⦃τ⦄⦄                                    := .β
    exact ℰ.bwds r₁' r₂' (hB₁ _ _ (soundVal hw σ τ hστ))
