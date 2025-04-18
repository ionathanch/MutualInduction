import CBPV.NormalInd

open ValType ComType Val Com

/-*--------------------------
  Logical relation on types
--------------------------*-/

section
set_option hygiene false
local notation:40 "⟦" A:41 "⟧ᵛ" "↘" P:41 => 𝒱 A P
local notation:40 "⟦" B:41 "⟧ᶜ" "↘" P:41 => 𝒞 B P

mutual
inductive 𝒱 : ValType → (Val → Prop) → Prop where
  | Unit : ⟦ Unit ⟧ᵛ ↘ (λ v ↦ SNeVal v ∨ v = unit)
  | Sum {A₁ A₂ P Q} :
    ⟦ A₁ ⟧ᵛ ↘ P →
    ⟦ A₂ ⟧ᵛ ↘ Q →
    ----------------------------------
    ⟦ Sum A₁ A₂ ⟧ᵛ ↘ (λ v ↦ SNeVal v ∨
      (∃ w, v = inl w ∧ P w) ∨
      (∃ w, v = inr w ∧ Q w))
  | U {B P} :
    ⟦ B ⟧ᶜ ↘ P →
    ------------------------------
    ⟦ U B ⟧ᵛ ↘ (λ v ↦ P (force v))

inductive 𝒞 : ComType → (Com → Prop) → Prop where
  | F {A P} :
    ⟦ A ⟧ᵛ ↘ P →
    ----------------------------------------------------------------------
    ⟦ F A ⟧ᶜ ↘ (λ m ↦ (∃ n, m ⤳⋆ n ∧ SNeCom n) ∨ (∃ v, m ⤳⋆ ret v ∧ P v))
  | Arr {A B P Q} :
    ⟦ A ⟧ᵛ ↘ P →
    ⟦ B ⟧ᶜ ↘ Q →
    ---------------------------------------------
    ⟦ Arr A B ⟧ᶜ ↘ (λ m ↦ ∀ v, P v → Q (app m v))
end
end

notation:40 "⟦" A:41 "⟧ᵛ" "↘" P:41 => 𝒱 A P
notation:40 "⟦" B:41 "⟧ᶜ" "↘" P:41 => 𝒞 B P

theorem interp :
  (∀ A, ∃ P, ⟦ A ⟧ᵛ ↘ P) ∧
  (∀ B, ∃ P, ⟦ B ⟧ᶜ ↘ P) := by
  refine ⟨λ A ↦ ?val, λ B ↦ ?com⟩
  mutual_induction A, B
  case Unit => exact ⟨_, .Unit⟩
  case Sum ihA ihB =>
    let ⟨_, hA⟩ := ihA
    let ⟨_, hB⟩ := ihB
    exact ⟨_, .Sum hA hB⟩
  case U ih => let ⟨_, h⟩ := ih; exact ⟨_, .U h⟩
  case F ih => let ⟨_, h⟩ := ih; exact ⟨_, .F h⟩
  case Arr ihA ihB =>
    let ⟨_, hA⟩ := ihA
    let ⟨_, hB⟩ := ihB
    exact ⟨_, .Arr hA hB⟩

def ValType.interp : ∀ A, ∃ P, ⟦ A ⟧ᵛ ↘ P := _root_.interp.left
def ComType.interp : ∀ B, ∃ P, ⟦ B ⟧ᶜ ↘ P := _root_.interp.right

/-*-----------------------------------------------------
  Properties of the logical relation:
  * Interpretation of a type is deterministic
  * Backward closure wrt strong reduction
  * Interpretations contain all strongly neutral terms
  * Terms in interpretations are strongly normalizing
-----------------------------------------------------*-/

theorem determinism :
  (∀ {A P Q}, ⟦ A ⟧ᵛ ↘ P → ⟦ A ⟧ᵛ ↘ Q → P = Q) ∧
  (∀ {B P Q}, ⟦ B ⟧ᶜ ↘ P → ⟦ B ⟧ᶜ ↘ Q → P = Q) := by
  refine ⟨λ {A P Q} h ↦ ?val, λ {B P Q} h ↦ ?com⟩
  mutual_induction h, h
  case Unit => intro h; cases h; rfl
  case Sum ihA ihB =>
    intro h; cases h with | Sum hA hB => rw [ihA hA, ihB hB]
  case U ih =>
    intro h; cases h with | U hB => rw [ih hB]
  case F ih =>
    intro h; cases h with | F hA => rw [ih hA]
  case Arr ihA ihB =>
    intro h; cases h with | Arr hA hB => rw [ihA hA, ihB hB]

def 𝒱.det : ∀ {A P Q}, ⟦ A ⟧ᵛ ↘ P → ⟦ A ⟧ᵛ ↘ Q → P = Q := determinism.left
def 𝒞.det : ∀ {B P Q}, ⟦ B ⟧ᶜ ↘ P → ⟦ B ⟧ᶜ ↘ Q → P = Q := determinism.right

theorem 𝒞.closure {B P} {m n : Com} (h : ⟦ B ⟧ᶜ ↘ P) (r : m ⤳⋆ n) : P n → P m := by
  mutual_induction h generalizing m n
  all_goals intro p
  case F =>
    match p with
    | .inl ⟨_, r', sne⟩ => exact Or.inl ⟨_, .trans' r r', sne⟩
    | .inr ⟨_, r', pv⟩  => exact Or.inr ⟨_, .trans' r r', pv⟩
  case Arr hA _ ih => exact λ v pv ↦ ih (.app r) (p v pv)

theorem adequacy :
  (∀ {A P} {v : Val}, ⟦ A ⟧ᵛ ↘ P → (SNeVal v → P v) ∧ (P v → SNVal v)) ∧
  (∀ {B P} {m : Com}, ⟦ B ⟧ᶜ ↘ P → (SNeCom m → P m) ∧ (P m → SNCom m)) := by
  refine ⟨λ h ↦ ?val, λ h ↦ ?com⟩
  mutual_induction h, h
  case Unit =>
    refine ⟨λ sne ↦ Or.inl sne, λ sn ↦ ?_⟩
    cases sn
    case inl sne => let ⟨_, e⟩ := sne; subst e; exact .var
    case inr e => subst e; constructor
  case Sum ihl ihr v =>
    refine ⟨λ sne ↦ Or.inl sne, λ sne ↦ ?_⟩
    match sne with
    | .inl h => let ⟨_, e⟩ := h; subst e; exact .var
    | .inr (.inl ⟨_, e, pv⟩) => subst e; exact .inl (ihl.right pv)
    | .inr (.inr ⟨_, e, qv⟩) => subst e; exact .inr (ihr.right qv)
  case U ih v =>
    let ⟨sneval, snval⟩ := @ih (force v)
    exact ⟨λ sne ↦ sneval (.force sne),
           λ sn ↦ (snval sn).force_inv⟩
  case F ih m =>
    refine ⟨λ sne ↦ Or.inl ⟨_, .refl, sne⟩, λ sn ↦ ?_⟩
    match sn with
    | .inl ⟨_, r, sne⟩ => exact r.red (.ne sne)
    | .inr ⟨_, r, pv⟩  => exact r.red (.ret (ih.right pv))
  case Arr ihv ihm _ =>
    refine ⟨λ sne ↦ ?sne, λ sn ↦ ?sn⟩
    case sne m =>
      exact λ v pv ↦ ihm.left (.app sne (ihv.right pv))
    case sn =>
      exact extensionality (ihm.right (sn (var 0) (ihv.left .var)))

def 𝒱.sneVal {A P v} (h : ⟦ A ⟧ᵛ ↘ P) : SNeVal v → P v := (adequacy.left h).left
def 𝒞.sneCom {B P m} (h : ⟦ B ⟧ᶜ ↘ P) : SNeCom m → P m := (adequacy.right h).left
def 𝒱.snVal {A P v} (h : ⟦ A ⟧ᵛ ↘ P) : P v → SNVal v := (adequacy.left h).right
def 𝒞.snCom {B P m} (h : ⟦ B ⟧ᶜ ↘ P) : P m → SNCom m := (adequacy.right h).right
