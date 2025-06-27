import CBPV.Commutation

open Nat ValType ComType Val Com

/-*-----------------------------------
  A-normal translation continuations
-----------------------------------*-/

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

@[simp]
def renameK (ξ : Nat → Nat) : K → K
  | .nil => .nil
  | .app v k => .app (renameVal ξ v) (renameK ξ k)
  | .letin m => .letin (renameCom (lift ξ) m)
  | .fst k => .fst (renameK ξ k)
  | .snd k => .snd (renameK ξ k)

@[simp]
def substK (σ : Nat → Val) : K → K
  | .nil => .nil
  | .app v k => .app (substVal σ v) (substK σ k)
  | .letin m => .letin (substCom (⇑ σ) m)
  | .fst k => .fst (substK σ k)
  | .snd k => .snd (substK σ k)

theorem substPlug {σ n k} : substCom σ (plug n k) = plug (substCom σ n) (substK σ k) := by
  induction k generalizing n <;> simp
  case app ih | fst ih | snd ih => simp [ih]

theorem substRenameK {ξ σ k} : substK σ (renameK ξ k) = substK (σ ∘ ξ) k := by
  induction k <;> simp [-lift, -up]
  case app v _ ih => exact ⟨substRenameVal _ _ v, ih⟩
  case letin m => exact (substRename _ _ _ (upLift _ _ _ (λ _ ↦ rfl))).right m
  case fst ih | snd ih => exact ih

/-*---------------------
  Typing continuations
---------------------*-/

section
set_option hygiene false
open K
local notation:40 Γ:41 "⊢" k:41 "∶" B₁:41 "⇒" B₂:41 => wtK Γ k B₁ B₂
inductive wtK : Ctxt → K → ComType → ComType → Prop where
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
notation:40 Γ:41 "⊢" k:41 "∶" B₁:41 "⇒" B₂:41 => wtK Γ k B₁ B₂

theorem wtK.rename {ξ k B₁ B₂} {Γ Δ : Ctxt} (hξ : Δ ⊢ ξ ∶ Γ) (h : Γ ⊢ k ∶ B₁ ⇒ B₂) :
  Δ ⊢ renameK ξ k ∶ B₁ ⇒ B₂ := by
  induction h generalizing ξ Δ
  all_goals constructor <;> apply_rules [wtRenameVal, wtRenameCom, wRenameLift]

theorem wtK.weaken {Γ k A B₁ B₂} : Γ ⊢ k ∶ B₁ ⇒ B₂ → Γ ∷ A ⊢ renameK succ k ∶ B₁ ⇒ B₂ :=
  wtK.rename wRenameSucc

theorem wtK.plug {Γ n k B₁ B₂}
  (hk : Γ ⊢ k ∶ B₁ ⇒ B₂) (h : Γ ⊢ n ∶ B₁) : Γ ⊢ (k [ n ]) ∶ B₂ := by
  induction hk generalizing n
  case nil => exact h
  case app hv _ hn => exact hn (.app h hv)
  case letin hm => exact .letin h hm
  case fst hn => exact hn (.fst h)
  case snd hn => exact hn (.snd h)

/-*-------------------------------------
  Logical equivalence of continuations
-------------------------------------*-/

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

/-*--------------------------------------
  Semantic equivalence of continuations
--------------------------------------*-/

@[reducible, simp] def semK Γ k₁ k₂ B₁ B₂ := ∀ σ τ, Γ ⊨ σ ~ τ → (substK σ k₁, substK τ k₂) ∈ ⟦B₁ ⇒ B₂⟧ᵏ
notation:40 Γ:41 "⊨" k₁:41 "~" k₂:41 "∶" B₁:41 "⇒" B₂:41 => semK Γ k₁ k₂ B₁ B₂

def semK.nil {Γ B} : Γ ⊨ .nil ~ .nil ∶ B ⇒ B := λ _ _ _ ↦ 𝒦.nil
def semK.fst {Γ k₁ k₂ B₁ B₂ B₃} (h : Γ ⊨ k₁ ~ k₂ ∶ B₁ ⇒ B₃) : Γ ⊨ .fst k₁ ~ .fst k₂ ∶ Prod B₁ B₂ ⇒ B₃ :=
  λ σ τ hστ ↦ 𝒦.fst (h σ τ hστ)
def semK.snd {Γ k₁ k₂ B₁ B₂ B₃} (h : Γ ⊨ k₁ ~ k₂ ∶ B₂ ⇒ B₃) : Γ ⊨ .snd k₁ ~ .snd k₂ ∶ Prod B₁ B₂ ⇒ B₃ :=
  λ σ τ hστ ↦ 𝒦.snd (h σ τ hστ)

theorem semK.app {Γ v w k₁ k₂ B₁ B₂} {A : ValType} (hA : Γ ⊨ v ~ w ∶ A) (h : Γ ⊨ k₁ ~ k₂ ∶ B₁ ⇒ B₂) : Γ ⊨ .app v k₁ ~ .app w k₂ ∶ Arr A B₁ ⇒ B₂ :=
  λ σ τ hστ ↦ 𝒦.app (hA σ τ hστ) (h σ τ hστ)

theorem semK.letin {Γ m₁ m₂ A} {B : ComType} (h : Γ ∷ A ⊨ m₁ ~ m₂ ∶ B) : Γ ⊨ .letin m₁ ~ .letin m₂ ∶ F A ⇒ B := by
  intro σ τ hστ; apply 𝒦.letin; intro v w hA; rw [← substUnion, ← substUnion]
  exact h (v +: σ) (w +: τ) (semCtxt.cons hA hστ)

theorem semK.rename {ξ k₁ k₂ B₁ B₂} {Γ Δ : Ctxt} (hξ : Γ ⊢ ξ ∶ Δ) (h : Δ ⊨ k₁ ~ k₂ ∶ B₁ ⇒ B₂) : Γ ⊨ renameK ξ k₁ ~ renameK ξ k₂ ∶ B₁ ⇒ B₂ := by
  intro σ τ hστ; rw [substRenameK, substRenameK]; exact h _ _ (semCtxt.rename hξ hστ)

theorem semK.weaken {Γ k₁ k₂ A B₁ B₂} (h : Γ ⊨ k₁ ~ k₂ ∶ B₁ ⇒ B₂) : Γ ∷ A ⊨ renameK succ k₁ ~ renameK succ k₂ ∶ B₁ ⇒ B₂ :=
  semK.rename wRenameSucc h

/-*--------------------------------------------------------------
  Fundamental theorem for semantic equivalence of continuations
--------------------------------------------------------------*-/

theorem soundK {Γ k B₁ B₂} (h : Γ ⊢ k ∶ B₁ ⇒ B₂) : Γ ⊨ k ~ k ∶ B₁ ⇒ B₂ := by
  induction h <;> intro σ τ hστ
  case nil => exact .nil
  case app hv _ ih => exact .app (soundVal hv σ τ hστ) (ih σ τ hστ)
  case letin hm =>
    refine .letin (λ v w hA ↦ ?_)
    rw [← substUnion, ← substUnion]
    refine soundCom hm (v +: σ) (w +: τ) (semCtxt.cons hA hστ)
  case fst ih => exact .fst (ih σ τ hστ)
  case snd ih => exact .snd (ih σ τ hστ)

/-*----------------------------------------------
  Semantic equivalence of plugged continuations
----------------------------------------------*-/

theorem 𝒦.semPlug {n₁ n₂ k₁ k₂ B₁ B₂} (hk : (k₁, k₂) ∈ ⟦B₁ ⇒ B₂⟧ᵏ) (hn : (n₁, n₂) ∈ ⟦B₁⟧ᵉ) : ((k₁[n₁]), (k₂[n₂])) ∈ ⟦B₂⟧ᵉ := by
  unfold 𝒦 at hk
  match hk with
  | .inl ⟨eB, ek₁, ek₂⟩ => subst eB; rw [ek₁, ek₂]; exact hn
  | .inr hk =>
  mutual_induction B₁ generalizing k₁ k₂ n₁ n₂
  case F =>
    unfold 𝒦' at hk
    let ⟨m, n, hB₂, ek₁, ek₂⟩ := hk
    let ⟨v, w, rv, rw, hA⟩ := hn.ret_inv
    specialize hB₂ v w hA
    rw [ek₁, ek₂]
    refine ℰ.bwds ?_ ?_ hB₂
    . exact .trans' (Evals.let rv) (.once .ζ)
    . exact .trans' (Evals.let rw) (.once .ζ)
  case Arr B₁ ih _ =>
    unfold 𝒦' at hk
    let ⟨v, w, k₁', k₂', hA, hk, ek₁, ek₂⟩ := hk
    let ⟨m, n, rm, rn, hB⟩ := hn.lam_inv
    have happ : (.app n₁ v, .app n₂ w) ∈ ⟦B₁⟧ᵉ := ℰ.bwds
      (.trans' (Evals.app rm) (.once .β))
      (.trans' (Evals.app rn) (.once .β))
      (hB v w hA)
    rw [ek₁, ek₂]; unfold 𝒦 at hk
    match hk with
    | .inl ⟨eB₂, ek₁, ek₂⟩ => subst eB₂ ek₁ ek₂; exact happ
    | .inr hk => unfold plug; exact ih happ (.inr hk) hk
  case Prod B₁ B₂ ihB₁ ihB₂ _ =>
    unfold 𝒦' at hk
    match hk with
    | .inl ⟨k₁, k₂, hk, ek₁, ek₂⟩ =>
      let ⟨_, _, _, _, r₁, r₂, hB₁⟩ := hn.fst
      have hfst : (.fst n₁, .fst n₂) ∈ ⟦B₁⟧ᵉ := ℰ.bwds
        (.trans' (Evals.fst r₁) (.once .π1))
        (.trans' (Evals.fst r₂) (.once .π1)) hB₁
      rw [ek₁, ek₂]; unfold 𝒦 at hk
      match hk with
      | .inl ⟨eB, hk₁, hk₂⟩ => subst eB hk₁ hk₂; exact hfst
      | .inr hk => apply ihB₁ hfst (.inr hk) hk
    | .inr ⟨k₁, k₂, hk, ek₁, ek₂⟩ =>
      let ⟨_, _, _, _, r₁, r₂, hB₂⟩ := hn.snd
      have hsnd : (.snd n₁, .snd n₂) ∈ ⟦B₂⟧ᵉ := ℰ.bwds
        (.trans' (Evals.snd r₁) (.once .π2))
        (.trans' (Evals.snd r₂) (.once .π2)) hB₂
      rw [ek₁, ek₂]; unfold 𝒦 at hk
      match hk with
      | .inl ⟨eB, hk₁, hk₂⟩ => subst eB hk₁ hk₂; exact hsnd
      | .inr hk => unfold plug; apply ihB₂ hsnd (.inr hk) hk

theorem semK.plug {Γ n₁ n₂ k₁ k₂ B₁ B₂} (hk : Γ ⊨ k₁ ~ k₂ ∶ B₁ ⇒ B₂) (hn : Γ ⊨ n₁ ~ n₂ ∶ B₁) : Γ ⊨ (k₁[n₁]) ~ (k₂[n₂]) ∶ B₂ := by
  intro σ τ hστ
  rw [substPlug, substPlug]
  exact 𝒦.semPlug (hk σ τ hστ) (hn σ τ hστ)

theorem semPlug {Γ n₁ n₂ k B₁ B₂} (hk : Γ ⊢ k ∶ B₁ ⇒ B₂) (hn : Γ ⊨ n₁ ~ n₂ ∶ B₁) : Γ ⊨ (k [ n₁ ]) ~ (k [ n₂ ]) ∶ B₂ :=
  (soundK hk).plug hn

/-*--------------------------------------
  Plugging commutes with configurations
--------------------------------------*-/

theorem semKletin {Γ n m k B₁ B₂} (hk : Γ ⊢ k ∶ B₁ ⇒ B₂) (h : Γ ⊢ letin n m ∶ B₁) :
  Γ ⊨ (k [letin n m]) ~ letin n ((renameK succ k) [m]) ∶ B₂ := by
  induction hk generalizing n m
  case nil => exact soundCom h
  case app hv hk ih => apply semCom.trans (semPlug hk (appLet h hv)) (ih (wtLetApp h hv))
  case letin hm => simp [-semCom, -lift]; exact letLet h hm
  case fst hk ih => apply semCom.trans (semPlug hk (fstLet h)) (ih (wtLetFst h))
  case snd hk ih => apply semCom.trans (semPlug hk (sndLet h)) (ih (wtLetSnd h))

theorem semKcase {Γ v m₁ m₂ k B₁ B₂} (hk : Γ ⊢ k ∶ B₁ ⇒ B₂) (h : Γ ⊢ case v m₁ m₂ ∶ B₁) :
  Γ ⊨ (k [case v m₁ m₂]) ~ case v ((renameK succ k) [m₁]) ((renameK succ k) [m₂]) ∶ B₂ := by
  induction hk generalizing v m₁ m₂
  case nil => exact soundCom h
  case app hv hk ih => apply semCom.trans (semPlug hk (appCase h hv)) (ih (wtCaseApp h hv))
  case letin hm => simp [-semCom, -lift]; exact letCase h hm
  case fst hk ih => apply semCom.trans (semPlug hk (fstCase h)) (ih (wtCaseFst h))
  case snd hk ih => apply semCom.trans (semPlug hk (sndCase h)) (ih (wtCaseSnd h))

/-*-----------------------------
  A-normal translation of CBPV
-----------------------------*-/

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

/-*-----------------------------------------------------------
  Soundness of A-normal translation wrt semantic equivalence
-----------------------------------------------------------*-/

theorem soundA {Γ} :
  (∀ {v} {A : ValType}, Γ ⊢ v ∶ A → Γ ⊨ v ~ ⟦v⟧ᵥ ∶ A) ∧
  (∀ {m k₁ k₂} {B₁ B₂ : ComType}, Γ ⊢ m ∶ B₁ → Γ ⊢ k₁ ∶ B₁ ⇒ B₂ →
    Γ ⊨ k₁ ~ k₂ ∶ B₁ ⇒ B₂ → Γ ⊨ (k₁[m]) ~ ⟦m⟧ₘ k₂ ∶ B₂) := by
  refine ⟨λ h ↦ ?val, λ h wtk hk ↦ ?com⟩
  mutual_induction h, h
  case force ih _ _ _ =>
    refine hk.plug (λ σ τ hστ ↦ ?_)
    unfold semVal 𝒱 at ih
    let ⟨_, _, h, em, en⟩ := ih σ τ hστ
    simp [-ℰ, em, en]; exact ℰ.bwd .π .π h
  case lam ih B _ _ =>
    refine hk.plug (λ σ τ hστ ↦ ℰ.lam (λ v w hA ↦ ?_))
    rw [← substUnion, ← substUnion]
    exact ih .nil (soundK .nil) (v +: σ) (w +: τ) (semCtxt.cons hA hστ)
  case app hv ihm ihv k₁ k₂ _ => exact ihm (.app hv wtk) (.app ihv hk)
  case ret ih _ _ _ => exact hk.plug (λ σ τ hστ ↦ ℰ.ret (ih σ τ hστ))
  case letin hn hm ihn ihm _ _ _ =>
    refine .trans (semKletin wtk (.letin hn hm)) ?_
    exact ihn
      (.letin (wtk.weaken.plug hm))
      (.letin (ihm wtk.weaken hk.weaken))
  case case hv hm₁ hm₂ ihv ihm₁ ihm₂ _ _ _ =>
    refine .trans (semKcase wtk (.case hv hm₁ hm₂)) (λ σ τ hστ ↦ ?_)
    unfold semVal 𝒱 at ihv
    match ihv σ τ hστ with
    | .inl ⟨v, w, hA₁, ev, ew⟩ =>
      simp [-up, -ℰ, ev, ew]
      refine ℰ.bwd ?_ ?_ (ihm₁ wtk.weaken hk.weaken (v +: σ) (w +: τ) (semCtxt.cons hA₁ hστ))
      all_goals rw [substUnion]; exact .ιl
    | .inr ⟨v, w, hA₂, ev, ew⟩ =>
      simp [-up, -ℰ, ev, ew]
      refine ℰ.bwd ?_ ?_ (ihm₂ wtk.weaken hk.weaken (v +: σ) (w +: τ) (semCtxt.cons hA₂ hστ))
      all_goals rw [substUnion]; exact .ιr
  case prod ihn₁ ihn₂ _ _ _ =>
    refine hk.plug (λ σ τ hστ ↦ ?_)
    exact ℰ.prod (ihn₁ .nil (soundK .nil) σ τ hστ) (ihn₂ .nil (soundK .nil) σ τ hστ)
  case fst ih _ _ _ => exact ih (.fst wtk) (.fst hk)
  case snd ih _ _ _ => exact ih (.snd wtk) (.snd hk)
  all_goals intro σ τ hστ
  case var mem => exact hστ mem
  case unit => exact 𝒱.unit
  case inl ih => exact 𝒱.inl (ih σ τ hστ)
  case inr ih => exact 𝒱.inr (ih σ τ hστ)
  case thunk ih => exact 𝒱.thunk (ih .nil (soundK .nil) σ τ hστ)

theorem soundAnil {Γ m} {B : ComType} (h : Γ ⊢ m ∶ B) : Γ ⊨ m ~ ⟦m⟧ₘ ∶ B :=
  soundA.right h .nil .nil

theorem retUnitA {m} (h : ⬝ ⊢ m ∶ F Unit) : ⟦m⟧ₘ ⇒⋆ ret unit := by
  let hm := soundAnil h var var semCtxt.nil
  rw [substComId, substComId] at hm
  unfold ℰ 𝒞 𝒱 at hm
  let ⟨_, _, _, ⟨r, _⟩, ⟨_, _, ⟨eu₁, eu₂⟩, eret₁, eret₂⟩⟩ := hm
  subst eu₁ eu₂ eret₁ eret₂; exact r
