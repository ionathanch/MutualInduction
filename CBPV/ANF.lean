import CBPV.CK
import CBPV.Typing

open Nat ValType ComType

/-*--------------------------------
  A-normal form of CBPV language:
  syntax and typing
--------------------------------*-/

namespace ANF

/-* Values, computations, and configurations *-/

mutual
inductive Val : Type where
  | var : Nat → Val
  | unit : Val
  | inl : Val → Val
  | inr : Val → Val
  | thunk : Cfg → Val

inductive Com : Type where
  | force : Val → Com
  | lam : Cfg → Com
  | app : Com → Val → Com
  | ret : Val → Com
  | prod : Cfg → Cfg → Com
  | fst : Com → Com
  | snd : Com → Com

inductive Cfg : Type where
  | com : Com → Cfg
  | letin : Com → Cfg → Cfg
  | case : Val → Cfg → Cfg → Cfg
end
open Val Com Cfg

/-* Renaming and substitution *-/

mutual
@[simp]
def renameVal (ξ : Nat → Nat) : Val → Val
  | var s => var (ξ s)
  | unit => unit
  | inl v => inl (renameVal ξ v)
  | inr v => inr (renameVal ξ v)
  | thunk m => thunk (renameCfg ξ m)

@[simp]
def renameCom (ξ : Nat → Nat) : Com → Com
  | force v => force (renameVal ξ v)
  | lam m => lam (renameCfg (lift ξ) m)
  | app n v => app (renameCom ξ n) (renameVal ξ v)
  | ret v => ret (renameVal ξ v)
  | prod m₁ m₂ => prod (renameCfg ξ m₁) (renameCfg ξ m₂)
  | fst n => fst (renameCom ξ n)
  | snd n => snd (renameCom ξ n)

@[simp]
def renameCfg (ξ : Nat → Nat) : Cfg → Cfg
  | com n => com (renameCom ξ n)
  | letin n m => letin (renameCom ξ n) (renameCfg (lift ξ) m)
  | case v m₁ m₂ => case (renameVal ξ v) (renameCfg (lift ξ) m₁) (renameCfg (lift ξ) m₂)
end

theorem renameExt {ξ ζ} (h : ∀ x, ξ x = ζ x) :
  (∀ v, renameVal ξ v = renameVal ζ v) ∧
  (∀ n, renameCom ξ n = renameCom ζ n) ∧
  (∀ m, renameCfg ξ m = renameCfg ζ m) := by
  refine ⟨λ v ↦ ?val, λ n ↦ ?com, λ m ↦ ?cfg⟩
  mutual_induction v, n, m generalizing ξ ζ
  all_goals simp; try repeat' constructor
  all_goals apply_rules [liftExt]

def renameValExt {ξ ζ : Nat → Nat} {v} (h : ∀ x, ξ x = ζ x) := (renameExt h).left v
def renameCfgExt {ξ ζ : Nat → Nat} {m} (h : ∀ x, ξ x = ζ x) := (renameExt h).right.right m

theorem renameComp {ξ ζ ς} (h : ∀ x, (ξ ∘ ζ) x = ς x) :
  (∀ v, (renameVal ξ ∘ renameVal ζ) v = renameVal ς v) ∧
  (∀ n, (renameCom ξ ∘ renameCom ζ) n = renameCom ς n) ∧
  (∀ m, (renameCfg ξ ∘ renameCfg ζ) m = renameCfg ς m) := by
  refine ⟨λ v ↦ ?val, λ n ↦ ?com, λ m ↦ ?cfg⟩
  mutual_induction v, n, m generalizing ξ ζ ς
  all_goals simp; try repeat' constructor
  all_goals apply_rules [liftComp]

def renameValComp {ξ ζ ς : Nat → Nat} {v} (h : ∀ x, (ξ ∘ ζ) x = ς x) := (renameComp h).left v
def renameCfgComp {ξ ζ ς : Nat → Nat} {v} (h : ∀ x, (ξ ∘ ζ) x = ς x) := (renameComp h).right.right v

@[simp]
def up (σ : Nat → Val) : Nat → Val :=
  var 0 +: (renameVal succ ∘ σ)
prefix:95 "⇑" => up

mutual
@[simp]
def substVal (σ : Nat → Val) : Val → Val
  | var x => σ x
  | unit => unit
  | inl v => inl (substVal σ v)
  | inr v => inr (substVal σ v)
  | thunk m => thunk (substCfg σ m)

@[simp]
def substCom (σ : Nat → Val) : Com → Com
  | force v => force (substVal σ v)
  | lam m => lam (substCfg (⇑ σ) m)
  | app n v => app (substCom σ n) (substVal σ v)
  | ret v => ret (substVal σ v)
  | prod m₁ m₂ => prod (substCfg σ m₁) (substCfg σ m₂)
  | fst n => fst (substCom σ n)
  | snd n => snd (substCom σ n)

@[simp]
def substCfg (σ : Nat → Val) : Cfg → Cfg
  | com n => com (substCom σ n)
  | letin n m => letin (substCom σ n) (substCfg (⇑ σ) m)
  | case v m₁ m₂ => case (substVal σ v) (substCfg (⇑ σ) m₁) (substCfg (⇑ σ) m₂)
end

/-* Typing *-/

section
set_option hygiene false
local notation:40 Γ:41 "⊢ₐ" v:41 "∶" A:41 => ValWt Γ v A
local notation:40 Γ:41 "⊢ₐ" n:41 "∶" B:41 => ComWt Γ n B
local notation:40 Γ:41 "⊢ₐ" m:41 "∶" B:41 => CfgWt Γ m B

mutual
inductive ValWt : Ctxt → Val → ValType → Prop where
  | var {Γ x A} :
    Γ ∋ x ∶ A →
    -------------
    Γ ⊢ₐ var x ∶ A
  | unit {Γ} : Γ ⊢ₐ unit ∶ Unit
  | inl {Γ v} {A₁ A₂ : ValType} :
    Γ ⊢ₐ v ∶ A₁ →
    ---------------------
    Γ ⊢ₐ inl v ∶ Sum A₁ A₂
  | inr {Γ v} {A₁ A₂ : ValType} :
    Γ ⊢ₐ v ∶ A₂ →
    ---------------------
    Γ ⊢ₐ inr v ∶ Sum A₁ A₂
  | thunk {Γ B} {m : Cfg} :
    Γ ⊢ₐ m ∶ B →
    -----------------
    Γ ⊢ₐ thunk m ∶ U B

inductive ComWt : Ctxt → Com → ComType → Prop where
  | force {Γ v B} :
    Γ ⊢ₐ v ∶ U B →
    ---------------
    Γ ⊢ₐ force v ∶ B
  | lam {Γ A B} {m : Cfg} :
    Γ ∷ A ⊢ₐ m ∶ B →
    -------------------
    Γ ⊢ₐ lam m ∶ Arr A B
  | app {Γ v A B} {n : Com} :
    Γ ⊢ₐ n ∶ Arr A B →
    Γ ⊢ₐ v ∶ A →
    ---------------
    Γ ⊢ₐ app n v ∶ B
  | ret {Γ v} {A : ValType} :
    Γ ⊢ₐ v ∶ A →
    ---------------
    Γ ⊢ₐ ret v ∶ F A
  | prod {Γ B₁ B₂} {m₁ m₂ : Cfg} :
    Γ ⊢ₐ m₁ ∶ B₁ →
    Γ ⊢ₐ m₂ ∶ B₂ →
    ---------------------------
    Γ ⊢ₐ prod m₁ m₂ ∶ Prod B₁ B₂
  | fst {Γ B₁ B₂} {n : Com} :
    Γ ⊢ₐ n ∶ Prod B₁ B₂ →
    ---------------
    Γ ⊢ₐ fst n ∶ B₁
  | snd {Γ B₁ B₂} {n : Com} :
    Γ ⊢ₐ n ∶ Prod B₁ B₂ →
    ---------------
    Γ ⊢ₐ snd n ∶ B₂

inductive CfgWt : Ctxt → Cfg → ComType → Prop where
  | com {Γ B} {n : Com} :
    Γ ⊢ₐ n ∶ B →
    -------------
    Γ ⊢ₐ com n ∶ B
  | letin {Γ A B} {n : Com} {m : Cfg} :
    Γ ⊢ₐ n ∶ F A →
    Γ ∷ A ⊢ₐ m ∶ B →
    -----------------
    Γ ⊢ₐ letin n m ∶ B
  | case {Γ v A₁ A₂ B} {m₁ m₂ : Cfg} :
    Γ ⊢ₐ v ∶ Sum A₁ A₂ →
    Γ ∷ A₁ ⊢ₐ m₁ ∶ B →
    Γ ∷ A₂ ⊢ₐ m₂ ∶ B →
    --------------------
    Γ ⊢ₐ case v m₁ m₂ ∶ B
end
end

notation:40 Γ:41 "⊢ₐ" v:41 "∶" A:41 => ValWt Γ v A
notation:40 Γ:41 "⊢ₐ" n:41 "∶" B:41 => ComWt Γ n B
notation:40 Γ:41 "⊢ₐ" m:41 "∶" B:41 => CfgWt Γ m B

/-* Renaming and weakening lemmas *-/

theorem wtRenameA {ξ} {Γ Δ : Ctxt} (hξ : Δ ⊢ ξ ∶ Γ) :
  (∀ {v : ANF.Val} {A}, Γ ⊢ₐ v ∶ A → Δ ⊢ₐ ANF.renameVal ξ v ∶ A) ∧
  (∀ {m : ANF.Com} {B}, Γ ⊢ₐ m ∶ B → Δ ⊢ₐ ANF.renameCom ξ m ∶ B) ∧
  (∀ {m : ANF.Cfg} {B}, Γ ⊢ₐ m ∶ B → Δ ⊢ₐ ANF.renameCfg ξ m ∶ B) := by
  refine ⟨λ h ↦ ?wtv, λ h ↦ ?wtn, λ h ↦ ?wtm⟩
  mutual_induction h, h, h generalizing ξ Δ
  all_goals constructor
  all_goals apply_rules [wRenameLift]

theorem wtRenameVal {ξ} {Γ Δ : Ctxt} {v : ANF.Val} {A} :
  Δ ⊢ ξ ∶ Γ → Γ ⊢ₐ v ∶ A → Δ ⊢ₐ ANF.renameVal ξ v ∶ A :=
  λ hξ ↦ (wtRenameA hξ).left

theorem wtRenameCfg {ξ} {Γ Δ : Ctxt} {m : ANF.Cfg} {B} :
  Δ ⊢ ξ ∶ Γ → Γ ⊢ₐ m ∶ B → Δ ⊢ₐ ANF.renameCfg ξ m ∶ B :=
  λ hξ ↦ (wtRenameA hξ).right.right

/-* The translation continuation and plugging into a continuation *-/

inductive K : Type where
  | nil : K
  | app : ANF.Val → K → K
  | letin : ANF.Cfg → K
  | fst : K → K
  | snd : K → K

@[simp]
def plug (n : ANF.Com) : K → ANF.Cfg
  | .nil => .com n
  | .app v k => plug (.app n v) k
  | .letin m => .letin n m
  | .fst k => plug (.fst n) k
  | .snd k => plug (.snd n) k
notation:40 k:41 "[" n:41 "]" => plug n k

/-* Renaming continuations *-/

@[simp]
def renameK (ξ : Nat → Nat) : K → K
  | .nil => .nil
  | .app v k => .app (ANF.renameVal ξ v) (renameK ξ k)
  | .letin m => .letin (ANF.renameCfg (lift ξ) m)
  | .fst k => .fst (renameK ξ k)
  | .snd k => .snd (renameK ξ k)

theorem renameKExt {ξ ζ k} (h : ∀ x, ξ x = ζ x) : renameK ξ k = renameK ζ k := by
  induction k <;> simp [-lift]
  case app ih => exact ⟨ANF.renameValExt h, ih⟩
  case letin => exact ANF.renameCfgExt (liftExt ξ ζ h)
  case fst ih | snd ih => exact ih

theorem renameKComp' {ξ ζ ς k} (h : ∀ x, (ξ ∘ ζ) x = ς x) :
  (renameK ξ ∘ renameK ζ) k = renameK ς k := by
  induction k <;> simp [-lift]
  case app ih => exact ⟨ANF.renameValComp h, ih⟩
  case letin => exact ANF.renameCfgComp (liftComp ξ ζ ς h)
  case fst ih | snd ih => exact ih

theorem renameKComp {ξ ζ k} : renameK ξ (renameK ζ k) = renameK (ξ ∘ ζ) k :=
  renameKComp' (λ _ ↦ rfl)

theorem renameKLiftSucc {ξ k} : renameK succ (renameK ξ k) = renameK (lift ξ) (renameK succ k) := by
  calc renameK succ (renameK ξ k)
    _ = renameK (succ ∘ ξ) k              := renameKComp
    _ = renameK (lift ξ ∘ succ) k         := by rw [← renameKExt (liftSucc ξ)]
    _ = renameK (lift ξ) (renameK succ k) := Eq.symm renameKComp

theorem renamePlug {ξ n k} : ANF.renameCfg ξ (plug n k) = plug (ANF.renameCom ξ n) (renameK ξ k) := by
  induction k generalizing n <;> simp
  case app ih | fst ih | snd ih => simp [ih]

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
    Γ ⊢ₐ v ∶ A →
    Γ ⊢ k ∶ B₁ ⇒ B₂ →
    -----------------------------
    Γ ⊢ app v k ∶ (Arr A B₁) ⇒ B₂
  | letin {Γ A} {m : ANF.Cfg} {B : ComType} :
    Γ ∷ A ⊢ₐ m ∶ B →
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

/-* Renaming and weakening lemmas for continuations *-/

theorem wtRenameK {ξ} {Γ Δ : Ctxt} {k B₁ B₂}
  (hξ : Δ ⊢ ξ ∶ Γ) (h : Γ ⊢ k ∶ B₁ ⇒ B₂) : Δ ⊢ renameK ξ k ∶ B₁ ⇒ B₂ := by
  induction h <;> constructor
  all_goals apply_rules [wtRenameVal, wtRenameCfg, wRenameLift]

theorem wtWeakenK {Γ k A B₁ B₂} :
  Γ ⊢ k ∶ B₁ ⇒ B₂ → Γ ∷ A ⊢ renameK succ k ∶ B₁ ⇒ B₂ :=
  wtRenameK wRenameSucc

theorem wtPlug {Γ k B₁ B₂} {n : ANF.Com}
  (hk : Γ ⊢ k ∶ B₁ ⇒ B₂) (h : Γ ⊢ₐ n ∶ B₁) : Γ ⊢ₐ (k [ n ]) ∶ B₂ := by
  induction hk generalizing n
  case nil => exact .com h
  case app hv _ hn => exact hn (.app h hv)
  case letin hm => exact .letin h hm
  case fst hn => exact hn (.fst h)
  case snd hn => exact hn (.snd h)
end ANF

/-*-----------------------------
  A-normal translation of CBPV
-----------------------------*-/

open Val Com

section
set_option hygiene false
local notation:40 "⟦" v:41 "⟧ᵥ" => Aval v
local notation:40 "⟦" m:41 "⟧ₘ" => Acom .nil m
local notation:40 "⟦" m:41 "⟧ₘ" k:41 => Acom k m
mutual
@[simp]
def Aval : Val → ANF.Val
  | var x => .var x
  | unit => .unit
  | inl v => .inl (⟦ v ⟧ᵥ)
  | inr v => .inr (⟦ v ⟧ᵥ)
  | thunk m => .thunk (⟦ m ⟧ₘ)

@[simp]
def Acom (k : ANF.K) : Com → ANF.Cfg
  | force v => k [ .force (⟦ v ⟧ᵥ) ]
  | ret v   => k [ .ret (⟦ v ⟧ᵥ) ]
  | lam m   => k [ .lam (⟦ m ⟧ₘ) ]
  | app n v   => ⟦ n ⟧ₘ .app (⟦ v ⟧ᵥ) k
  | letin n m => ⟦ n ⟧ₘ .letin (⟦ m ⟧ₘ (ANF.renameK succ k))
  | case v m₁ m₂ => .case (⟦ v ⟧ᵥ) (⟦ m₁ ⟧ₘ (ANF.renameK succ k)) (⟦ m₂ ⟧ₘ (ANF.renameK succ k))
  | prod m₁ m₂ => k [ .prod (⟦ m₁ ⟧ₘ) (⟦ m₂ ⟧ₘ) ]
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
notation:40 "⟦" v:41 "⟧ᵥ" => Aval v
notation:40 "⟦" m:41 "⟧ₘ" => Acom K.nil m
notation:40 "⟦" m:41 "⟧ₘ" k:41 => Acom k m

/-* Renaming commutes with A-normalization *-/

theorem renameA {ξ} :
  (∀ v, (⟦ renameVal ξ v ⟧ᵥ) = ANF.renameVal ξ (⟦ v ⟧ᵥ)) ∧
  (∀ m k, (⟦ renameCom ξ m ⟧ₘ (ANF.renameK ξ k)) = ANF.renameCfg ξ (⟦ m ⟧ₘ k)) := by
  refine ⟨λ v ↦ ?val, λ m k ↦ ?com⟩
  mutual_induction v, m generalizing ξ
  case var | unit => rfl
  case inl ih | inr ih => simp [ih]
  case thunk ih => simp; exact ih .nil
  case force ih | ret ih => simp [ih, ANF.renamePlug]
  case lam ih =>
    have e := ih (ξ := lift ξ) .nil
    simp [-lift] at *; rw [e]; simp [ANF.renamePlug]
  case app ihm ihv => simp [-lift, ihv, ← ihm]
  case letin ihn ihm =>
    simp [-lift, ← ihn, ← ihm, ANF.renameKLiftSucc]
  case case ihv ihm₁ ihm₂ =>
    simp [-lift, ihv, ← ihm₁, ← ihm₂, ANF.renameKLiftSucc]
  case prod ihm₁ ihm₂ => simp [← ihm₁, ← ihm₂, ANF.renamePlug]
  case fst ih | snd ih => simp [← ih]

theorem renameAval {ξ v} : (⟦ renameVal ξ v ⟧ᵥ) = ANF.renameVal ξ (⟦ v ⟧ᵥ) := renameA.left v
theorem renameAcom {ξ m k} : (⟦ renameCom ξ m ⟧ₘ (ANF.renameK ξ k)) = ANF.renameCfg ξ (⟦ m ⟧ₘ k) := renameA.right m k

/-* Translation is type preserving *-/

theorem preservation {Γ} :
  (∀ {v} {A : ValType}, Γ ⊢ v ∶ A → Γ ⊢ₐ (⟦ v ⟧ᵥ) ∶ A) ∧
  (∀ {k m} {B₁ B₂ : ComType}, Γ ⊢ k ∶ B₁ ⇒ B₂ → Γ ⊢ m ∶ B₁ → Γ ⊢ₐ (⟦ m ⟧ₘ k) ∶ B₂) := by
  refine ⟨λ h ↦ ?val, λ hk h ↦ ?com⟩
  mutual_induction h, h
  case var mem => exact .var mem
  case unit => exact .unit
  case inl h => exact .inl h
  case inr h => exact .inr h
  case thunk h => exact .thunk (h .nil)
  case force h _ _ => exact (ANF.wtPlug hk (.force h))
  case ret h _ _ => exact (ANF.wtPlug hk (.ret h))
  case lam h _ _ => exact (ANF.wtPlug hk (.lam (h .nil)))
  case app hn hv k _ => exact hn (.app hv hk)
  case letin hn hm _ _ => exact hn (.letin (hm (ANF.wtWeakenK hk)))
  case case hv hm₁ hm₂ _ _ => exact .case hv (hm₁ (ANF.wtWeakenK hk)) (hm₂ (ANF.wtWeakenK hk))
  case prod hm₁ hm₂ _ _ => exact ANF.wtPlug hk (.prod (hm₁ .nil) (hm₂ .nil))
  case fst h _ _ => exact h (.fst hk)
  case snd h _ _ => exact h (.snd hk)

/-*----------------------------
  CK machine semantics of ANF
----------------------------*-/

namespace ANF

inductive F : Type where
  | app : Val → F
  | letin : Cfg → F
  | fst : F
  | snd : F
open F

def Kₐ := List F
def CK := Cfg × Kₐ

@[simp]
def renameKₐ (ξ : Nat → Nat) : Kₐ → Kₐ
  | [] => []
  | .app v :: k => .app (renameVal ξ v) :: renameKₐ ξ k
  | .letin m :: k => .letin (renameCfg (lift ξ) m) :: renameKₐ ξ k
  | .fst :: k => fst :: renameKₐ ξ k
  | .snd :: k => snd :: renameKₐ ξ k

@[simp]
def KKₐ : K → Kₐ
  | .nil => []
  | .app v k => .app v :: KKₐ k
  | .letin m => [.letin m]
  | .fst k => .fst :: KKₐ k
  | .snd k => .snd :: KKₐ k
notation:40 "⟦" k:41 "⟧ₖ" => KKₐ k

theorem renameKKₐ {k} (ξ : Nat → Nat) : (⟦ ANF.renameK ξ k ⟧ₖ) = renameKₐ ξ (⟦ k ⟧ₖ) := by
  induction k <;> simp <;> congr

section
set_option hygiene false
local infix:40 "⤳" => Step
inductive Step : CK → CK → Prop where
  | π {m k} :        ⟨.com (.force (.thunk m)), k⟩   ⤳ ⟨m, k⟩
  | β {m v k} :      ⟨.com (.lam m), .app v :: k⟩    ⤳ ⟨substCfg (v +: .var) m, k⟩
  | ζ {v m k} :      ⟨.com (.ret v), .letin m :: k⟩  ⤳ ⟨substCfg (v +: .var) m, k⟩
  | ιl {v m₁ m₂ k} : ⟨.case (.inl v) m₁ m₂, k⟩       ⤳ ⟨substCfg (v +: .var) m₁, k⟩
  | ιr {v m₁ m₂ k} : ⟨.case (.inr v) m₁ m₂, k⟩       ⤳ ⟨substCfg (v +: .var) m₂, k⟩
  | π1 {m₁ m₂ k} :   ⟨.com (.prod m₁ m₂), .fst :: k⟩ ⤳ ⟨m₁, k⟩
  | π2 {m₁ m₂ k} :   ⟨.com (.prod m₁ m₂), .snd :: k⟩ ⤳ ⟨m₂, k⟩
  | app {n v k} :    ⟨.com (.app n v), k⟩            ⤳ ⟨.com n, .app v :: k⟩
  | letin {n m k} :  ⟨.letin n m, k⟩                 ⤳ ⟨.com n, .letin m :: k⟩
  | fst {n k} :      ⟨.com (.fst n), k⟩              ⤳ ⟨.com n, .fst :: k⟩
  | snd {n k} :      ⟨.com (.snd n), k⟩              ⤳ ⟨.com n, .snd :: k⟩
end
infix:40 "⤳" => Step

@[reducible] def Steps := RTC Step
infix:40 "⤳⋆"  => Steps

end ANF

/-* Translating continuations *-/

@[simp]
def KKₐ : K → ANF.Kₐ
  | [] => []
  | .app v :: k => .app (⟦ v ⟧ᵥ) :: KKₐ k
  | .letin m :: k => .letin (⟦ m ⟧ₘ .nil) :: KKₐ k
  | .fst :: k => .fst :: KKₐ k
  | .snd :: k => .snd :: KKₐ k
notation:40 "⟦" k:41 "⟧ₖ" => KKₐ k

theorem renameKKₐ {k} (ξ : Nat → Nat) : (⟦ renameK ξ k ⟧ₖ) = ANF.renameKₐ ξ (⟦ k ⟧ₖ) := by
  induction k
  case nil => simp
  case cons f _ ih =>
    cases f <;> simp [-lift]
    case app => congr; exact renameAval
    case letin =>
      have e : ANF.K.nil = ANF.renameK (lift ξ) ANF.K.nil := rfl
      congr; rw [e]; exact renameAcom
    case fst | snd => simp [ih]

/-
@[simp]
def FK : K → ANF.K
  | [] => .nil
  | .app v :: fs => .app (⟦ v ⟧ᵥ) (FK fs)
  | .letin m :: fs => .letin (⟦ m ⟧ₘ ANF.renameK succ (FK fs))
  | _ => sorry

theorem renameFK {fs} (ξ : Nat → Nat) : FK (renameK ξ fs) = ANF.renameK ξ (FK fs) := by
  induction fs
  case nil => simp
  case cons f _ ih =>
    cases f <;> simp [-lift]
    case app => exact ⟨renameAval, ih⟩
    case letin => rw [ih, ANF.renameKLiftSucc, renameAcom]
-/

/-* Composing continuations *-/

@[simp]
def compKCfg (k : ANF.K) : ANF.Cfg → ANF.Cfg
  | .com n => ANF.plug n k
  | .letin n m => .letin n (compKCfg (ANF.renameK succ k) m)
  | .case v m₁ m₂ => .case v (compKCfg (ANF.renameK succ k) m₁) (compKCfg (ANF.renameK succ k) m₂)

@[simp]
def compKK (k : ANF.K) : ANF.K → ANF.K
  | .nil => k
  | .app v k' => .app v (compKK k k')
  | .letin m => .letin (compKCfg (ANF.renameK succ k) m)
  | .fst k' => .fst (compKK k k')
  | .snd k' => .snd (compKK k k')

theorem renameCompKCfg {ξ m k} : ANF.renameCfg ξ (compKCfg k m) = compKCfg (ANF.renameK ξ k) (ANF.renameCfg ξ m) := by
  mutual_induction m generalizing ξ k
  case com => simp [ANF.renamePlug]
  case letin ih => simp [ih, ANF.renameKLiftSucc]
  case case ihm₁ ihm₂ => simp [ihm₁, ihm₂, ANF.renameKLiftSucc]

theorem renameCompKK {ξ k₁ k₂} : ANF.renameK ξ (compKK k₁ k₂) = compKK (ANF.renameK ξ k₁) (ANF.renameK ξ k₂) := by
  induction k₂
  case nil => simp
  case app ih | fst ih | snd ih => simp [ih]
  case letin => simp [ANF.renameKLiftSucc, renameCompKCfg]

theorem compPlug {n k₁ k₂} : compKCfg k₁ (k₂ [ n ]) = ((compKK k₁ k₂) [ n ]) := by
  induction k₂ generalizing n <;> apply_assumption

theorem compA {m k₁ k₂} : compKCfg k₁ (⟦ m ⟧ₘ k₂) = (⟦ m ⟧ₘ (compKK k₁ k₂)) := by
  mutual_induction m generalizing k₁ k₂
  case force | lam | ret => exact compPlug
  case app ih | fst ih | snd ih => simp [ih]
  case letin ihn ihm => simp [ihn, ihm, renameCompKK]
  case case ihm₁ ihm₂ => simp [ihm₁, ihm₂, renameCompKK]
  case prod ihm₁ ihm₂ => simp [ihm₁, ihm₂, compPlug]

/-
@[simp]
def Asubst (σ : Nat → Val) : Nat → ANF.Val := λ x ↦ ⟦ σ x ⟧ᵥ
notation:40 "⟦" σ:41 "⟧ₛ" => Asubst σ

theorem Alookup {σ x} : (⟦ σ x ⟧ᵥ) = (⟦ σ ⟧ₛ) x := by
  cases x <;> simp

theorem Acons {σ v} : (⟦ v +: σ ⟧ₛ) = ((⟦ v ⟧ᵥ) +: (⟦ σ ⟧ₛ)) :=
  funext (λ x ↦ by cases x <;> simp)

def CEK := Com × (Nat → Val) × List F
def ACEK := ANF.Cfg × (Nat → ANF.Val) × List Fₐ

section
set_option hygiene false
local notation:40 cek:41 "⤳" cek':41 => eval cek cek'
inductive eval : CEK → CEK → Prop where
  | force {σ fs m}       : ⟨force (thunk m), σ, fs⟩    ⤳ ⟨m, σ, fs⟩
  | force' {σ fs x}      : ⟨force (var x), σ, fs⟩      ⤳ ⟨force (σ x), σ, fs⟩
  | lam {σ fs m v}       : ⟨lam m, σ, .app v :: fs⟩    ⤳ ⟨m, v +: σ, renameF succ fs⟩
  | app {σ fs m v}       : ⟨app m v, σ, fs⟩            ⤳ ⟨m, σ, .cons (.app v) fs⟩
  | ret {σ fs m v}       : ⟨ret v, σ, .letin m :: fs⟩  ⤳ ⟨m, v +: σ, renameF succ fs⟩
  | letin {σ fs n m}     : ⟨letin n m, σ, fs⟩          ⤳ ⟨n, σ, .cons (.letin m) fs⟩
  | case₁ {σ fs v m₁ m₂} : ⟨case (inl v) m₁ m₂, σ, fs⟩ ⤳ ⟨m₁, v +: σ, renameF succ fs⟩
  | case₂ {σ fs v m₁ m₂} : ⟨case (inr v) m₁ m₂, σ, fs⟩ ⤳ ⟨m₂, v +: σ, renameF succ fs⟩
  | case' {σ fs m₁ m₂ x} : ⟨case (var x) m₁ m₂, σ, fs⟩ ⤳ ⟨case (σ x) m₁ m₂, σ, fs⟩
end
notation:40 cek:41 "⤳" cek':41 => eval cek cek'

section
set_option hygiene false
local notation:40 acek:41 "⤳ₐ" acek':41 => aeval acek acek'
local notation:40 acek:41 "⤳ₐ⋆" acek':41 => aevals acek acek'

inductive aeval : ACEK → ACEK → Prop where
  | force {σ fs m}       : ⟨.com (.force (.thunk m)), σ, fs⟩  ⤳ₐ ⟨m, σ, fs⟩
  | force' {σ fs x}      : ⟨.com (.force (.var x)), σ, fs⟩    ⤳ₐ ⟨.com (.force (σ x)), σ, fs⟩
  | lam {σ fs m v}       : ⟨.com (.lam m), σ, .app v :: fs⟩   ⤳ₐ ⟨m, v +: σ, renameFₐ succ fs⟩
  | app {σ fs n v}       : ⟨.com (.app n v), σ, fs⟩           ⤳ₐ ⟨.com n, σ, .cons (.app v) fs⟩
  | ret {σ fs m v}       : ⟨.com (.ret v), σ, .letin m :: fs⟩ ⤳ₐ ⟨m, v +: σ, renameFₐ succ fs⟩
  | letin {σ fs n m}     : ⟨.letin n m, σ, fs⟩                ⤳ₐ ⟨.com n, σ, .cons (.letin m) fs⟩
  | case₁ {σ fs v m₁ m₂} : ⟨.case (.inl v) m₁ m₂, σ, fs⟩      ⤳ₐ ⟨m₁, v +: σ, renameFₐ succ fs⟩
  | case₂ {σ fs v m₁ m₂} : ⟨.case (.inr v) m₁ m₂, σ, fs⟩      ⤳ₐ ⟨m₂, v +: σ, renameFₐ succ fs⟩
  | case' {σ fs m₁ m₂ x} : ⟨.case (.var x) m₁ m₂, σ, fs⟩      ⤳ₐ ⟨.case (σ x) m₁ m₂, σ, fs⟩

inductive aevals : ACEK → ACEK → Prop where
  | refl {m σ fs} : ⟨m, σ, fs⟩ ⤳ₐ⋆ ⟨m, σ, fs⟩
  | trans {m₁ m₂ m₃ σ₁ σ₂ σ₃ fs₁ fs₂ fs₃} :
    ⟨m₁, σ₁, fs₁⟩ ⤳ₐ  ⟨m₂, σ₂, fs₂⟩ →
    ⟨m₂, σ₂, fs₂⟩ ⤳ₐ⋆ ⟨m₃, σ₃, fs₃⟩ →
    ⟨m₁, σ₁, fs₁⟩ ⤳ₐ⋆ ⟨m₃, σ₃, fs₃⟩
end

notation:40 acek:41 "⤳ₐ" acek':41 => aeval acek acek'
notation:40 acek:41 "⤳ₐ⋆" acek':41 => aevals acek acek'

theorem compositionality' {m σ fs k} : ⟨k [ m ], σ, fs⟩ ⤳ₐ⋆ ⟨.com m, σ, KFₐ k ++ fs⟩ := by
  induction k generalizing m
  case nil => exact .refl
  case app ih => exact .trans' ih aeval.app.aevals
  case letin => exact aeval.letin.aevals

theorem compositionality {m k σ fs} : ⟨compKCfg k m, σ, fs⟩ ⤳ₐ⋆ ⟨m, σ, KFₐ k ++ fs⟩ := by
  mutual_induction m
  case com => exact compositionality'
  case letin ih => simp; refine .trans .letin ?_; sorry
  case case ihm₁ ihm₂ => simp; sorry

theorem equivalence {m m' σ σ' fs fs'} (r : ⟨m, σ, fs⟩ ⤳ ⟨m', σ', fs'⟩) :
  ∀ fsₐ, ∃ fsₐ', ⟨⟦ m ⟧ₘ (FK fs), ⟦ σ ⟧ₛ, fsₐ⟩ ⤳ₐ⋆ ⟨⟦ m' ⟧ₘ (FK fs'), ⟦ σ' ⟧ₛ, fsₐ'⟩ := by
  intro fsₐ
  generalize e : (m, σ, fs) = cek, e' : (m', σ', fs') = cek' at r
  induction r
  all_goals injection e with em e; injection e with eσ ef; subst em eσ ef
  all_goals injection e' with em' e'; injection e' with eσ' ef'; subst em' eσ' ef'
  case force =>
    simp; exists fsₐ
    refine .trans' compositionality' ?_
    refine .trans .force ?_
    have e : FK fs' = compKK (FK fs') .nil := by rfl
    rw [e, ← compA, ← e]
    sorry
  case force' =>
    simp; exists fsₐ
    refine .trans' compositionality' ?_
    refine .trans .force' ?_
    rw [Alookup]
    sorry
  case lam fs _ =>
    rw [Acons]; simp; exists renameFₐ succ fsₐ
    refine .trans' compositionality' ?_
    refine .trans .app ?_
    refine .trans .lam ?_
    have e : FK (renameF succ fs) = compKK (FK (renameF succ fs)) .nil := by rfl
    rw [e, ← compA]
    sorry
  case app => exact ⟨_, .refl⟩
  case ret v => rw [Acons, renameFK]; exact ⟨_, .trans .letin (.trans .ret .refl)⟩
  case letin => simp; exists fsₐ; exact .refl
  case case₁ => rw [Acons, renameFK]; exact ⟨_, .trans .case₁ .refl⟩
  case case₂ => rw [Acons, renameFK]; exact ⟨_, .trans .case₂ .refl⟩
  case case' => exact ⟨_, aeval.case'.aevals⟩

theorem equivalence' {m m' σ σ' fs fs'} (r : ⟨m, σ, fs⟩ ⤳ ⟨m', σ', fs'⟩) :
  ⟨⟦ m ⟧ₘ .nil, ⟦ σ ⟧ₛ, FFₐ fs⟩ ⤳ₐ⋆ ⟨⟦ m' ⟧ₘ .nil, ⟦ σ' ⟧ₛ, FFₐ fs'⟩ := by
  generalize e : (m, σ, fs) = cek, e' : (m', σ', fs') = cek' at r
  induction r
  all_goals injection e with em e; injection e with eσ ef; subst em eσ ef
  all_goals injection e' with em' e'; injection e' with eσ' ef'; subst em' eσ' ef'
  all_goals try rw [Acons, renameFFₐ]
  case force | force' | lam | ret | case₁ | case₂ | case' =>
    apply aeval.aevals; constructor
  case app v =>
    have e : K.app (⟦ v ⟧ᵥ) .nil = compKK (K.app (⟦ v ⟧ᵥ) .nil) .nil := rfl
    simp; rw [e, ← compA]; exact compositionality
  case letin m =>
    have e : K.letin (⟦ m ⟧ₘ .nil) = compKK (K.letin (⟦ m ⟧ₘ .nil)) .nil := rfl
    simp; rw [e, ← compA]; exact compositionality
-/
