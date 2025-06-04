import CBPV.Typing

open ValType ComType

namespace ANF

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

inductive Cfg : Type where
  | com : Com → Cfg
  | letin : Com → Cfg → Cfg
  | case : Val → Cfg → Cfg → Cfg
end
open Val Com Cfg

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

theorem renameValExt {ξ ζ v} (h : ∀ x, ξ x = ζ x) : renameVal ξ v = renameVal ζ v :=
  (renameExt h).left v

theorem renameCfgExt {ξ ζ m} (h : ∀ x, ξ x = ζ x) : renameCfg ξ m = renameCfg ζ m :=
  (renameExt h).right.right m

theorem renameComp {ξ ζ ς} (h : ∀ x, (ξ ∘ ζ) x = ς x) :
  (∀ v, (renameVal ξ ∘ renameVal ζ) v = renameVal ς v) ∧
  (∀ n, (renameCom ξ ∘ renameCom ζ) n = renameCom ς n) ∧
  (∀ m, (renameCfg ξ ∘ renameCfg ζ) m = renameCfg ς m) := by
  refine ⟨λ v ↦ ?val, λ n ↦ ?com, λ m ↦ ?cfg⟩
  mutual_induction v, n, m generalizing ξ ζ ς
  all_goals simp; try repeat' constructor
  all_goals apply_rules [liftComp]

theorem renameValComp {ξ ζ ς v} (h : ∀ x, (ξ ∘ ζ) x = ς x) : renameVal ξ (renameVal ζ v) = renameVal ς v :=
  (renameComp h).left v

theorem renameCfgComp {ξ ζ ς m} (h : ∀ x, (ξ ∘ ζ) x = ς x) : renameCfg ξ (renameCfg ζ m) = renameCfg ς m :=
  (renameComp h).right.right m

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
end ANF

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

open Nat Val Com

inductive K : Type where
  | nil : K
  | app : ANF.Val → K → K
  | letin : ANF.Cfg → K

@[simp]
def renameK (ξ : Nat → Nat) : K → K
  | .nil => .nil
  | .app v k => .app (ANF.renameVal ξ v) (renameK ξ k)
  | .letin m => .letin (ANF.renameCfg (lift ξ) m)

theorem renameKExt {ξ ζ k} (h : ∀ x, ξ x = ζ x) : renameK ξ k = renameK ζ k := by
  induction k <;> simp [-lift]
  case app ih => exact ⟨ANF.renameValExt h, ih⟩
  case letin => exact ANF.renameCfgExt (liftExt ξ ζ h)

theorem renameKComp' {ξ ζ ς k} (h : ∀ x, (ξ ∘ ζ) x = ς x) :
  (renameK ξ ∘ renameK ζ) k = renameK ς k := by
  induction k <;> simp [-lift]
  case app ih => exact ⟨ANF.renameValComp h, ih⟩
  case letin => exact ANF.renameCfgComp (liftComp ξ ζ ς h)

theorem renameKComp {ξ ζ k} : renameK ξ (renameK ζ k) = renameK (ξ ∘ ζ) k :=
  renameKComp' (λ _ ↦ rfl)

theorem renameKLiftSucc {ξ k} : renameK succ (renameK ξ k) = renameK (lift ξ) (renameK succ k) := by
  calc renameK succ (renameK ξ k)
    _ = renameK (succ ∘ ξ) k              := renameKComp
    _ = renameK (lift ξ ∘ succ) k         := by rw [← renameKExt (liftSucc ξ)]
    _ = renameK (lift ξ) (renameK succ k) := Eq.symm renameKComp

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
end
notation:40 Γ:41 "⊢" k:41 "∶" B₁:41 "⇒" B₂:41 => KWt Γ k B₁ B₂

theorem wtRenameK {ξ} {Γ Δ : Ctxt} {k B₁ B₂}
  (hξ : Δ ⊢ ξ ∶ Γ) (h : Γ ⊢ k ∶ B₁ ⇒ B₂) : Δ ⊢ renameK ξ k ∶ B₁ ⇒ B₂ := by
  induction h <;> constructor
  all_goals apply_rules [wtRenameVal, wtRenameCfg, wRenameLift]

theorem wtWeakenK {Γ k A B₁ B₂} :
  Γ ⊢ k ∶ B₁ ⇒ B₂ → Γ ∷ A ⊢ renameK succ k ∶ B₁ ⇒ B₂ :=
  wtRenameK wRenameSucc

@[simp]
def plug (n : ANF.Com) : K → ANF.Cfg
  | .nil => .com n
  | .app v k => plug (.app n v) k
  | .letin m => .letin n m
notation:40 k:41 "[" n:41 "]" => plug n k

theorem plugWt {Γ k B₁ B₂} {n : ANF.Com}
  (hk : Γ ⊢ k ∶ B₁ ⇒ B₂) (h : Γ ⊢ₐ n ∶ B₁) : Γ ⊢ₐ (k [ n ]) ∶ B₂ := by
  induction hk generalizing n
  case nil => exact .com h
  case app hv _ hn => exact hn (.app h hv)
  case letin hm => exact .letin h hm

theorem renamePlug {ξ n k} : ANF.renameCfg ξ (plug n k) = plug (ANF.renameCom ξ n) (renameK ξ k) := by
  induction k generalizing n <;> simp
  case app ih => simp [ih]

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
def Acom (k : K) : Com → ANF.Cfg
  | force v => k [ .force (⟦ v ⟧ᵥ) ]
  | ret v   => k [ .ret (⟦ v ⟧ᵥ) ]
  | lam m   => k [ .lam (⟦ m ⟧ₘ) ]
  | app n v   => ⟦ n ⟧ₘ .app (⟦ v ⟧ᵥ) k
  | letin n m => ⟦ n ⟧ₘ .letin (⟦ m ⟧ₘ (renameK succ k))
  | case v m₁ m₂ => .case (⟦ v ⟧ᵥ) (⟦ m₁ ⟧ₘ (renameK succ k)) (⟦ m₂ ⟧ₘ (renameK succ k))
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

theorem renameA {ξ} :
  (∀ v, (⟦ renameVal ξ v ⟧ᵥ) = ANF.renameVal ξ (⟦ v ⟧ᵥ)) ∧
  (∀ m k, (⟦ renameCom ξ m ⟧ₘ (renameK ξ k)) = ANF.renameCfg ξ (⟦ m ⟧ₘ k)) := by
  refine ⟨λ v ↦ ?val, λ m k ↦ ?com⟩
  mutual_induction v, m generalizing ξ
  case val.var | val.unit => rfl
  case val.inl ih | val.inr ih => simp [ih]
  case val.thunk ih => simp; exact ih .nil
  case com.force ih | com.ret ih => simp [ih, renamePlug]
  case com.lam ih =>
    have e := ih (ξ := lift ξ) .nil
    simp [-lift] at *; rw [e]; simp [renamePlug]
  case com.app ihm ihv => simp [-lift, ihv, ← ihm]
  case com.letin ihn ihm =>
    simp [-lift, ← ihn, ← ihm, renameKLiftSucc]
  case com.case ihv ihm₁ ihm₂ =>
    simp [-lift, ihv, ← ihm₁, ← ihm₂, renameKLiftSucc]

theorem renameAval {ξ v} : (⟦ renameVal ξ v ⟧ᵥ) = ANF.renameVal ξ (⟦ v ⟧ᵥ) := renameA.left v
theorem renameAcom {ξ m k} : (⟦ renameCom ξ m ⟧ₘ (renameK ξ k)) = ANF.renameCfg ξ (⟦ m ⟧ₘ k) := renameA.right m k

@[simp]
def Asubst (σ : Nat → Val) : Nat → ANF.Val := λ x ↦ ⟦ σ x ⟧ᵥ
notation:40 "⟦" σ:41 "⟧ₛ" => Asubst σ

theorem Acons {σ v} : (⟦ v +: σ ⟧ₛ) = ((⟦ v ⟧ᵥ) +: (⟦ σ ⟧ₛ)) :=
  funext (λ x ↦ by cases x <;> simp)

theorem preservation {Γ} :
  (∀ {v} {A : ValType}, Γ ⊢ v ∶ A → Γ ⊢ₐ (⟦ v ⟧ᵥ) ∶ A) ∧
  (∀ {k m} {B₁ B₂ : ComType}, Γ ⊢ k ∶ B₁ ⇒ B₂ → Γ ⊢ m ∶ B₁ → Γ ⊢ₐ (⟦ m ⟧ₘ k) ∶ B₂) := by
  refine ⟨λ h ↦ ?val, λ hk h ↦ ?com⟩
  mutual_induction h, h
  case val.var mem => exact .var mem
  case val.unit => exact .unit
  case val.inl h => exact .inl h
  case val.inr h => exact .inr h
  case val.thunk h => exact .thunk (h .nil)
  case com.force h _ _ => exact (plugWt hk (.force h))
  case com.ret h _ _ => exact (plugWt hk (.ret h))
  case com.lam h _ _ => exact (plugWt hk (.lam (h .nil)))
  case com.app hn hv k _ => exact hn (.app hv hk)
  case com.letin hn hm _ _ => exact hn (.letin (hm (wtWeakenK hk)))
  case com.case hv hm₁ hm₂ _ _ => exact .case hv (hm₁ (wtWeakenK hk)) (hm₂ (wtWeakenK hk))

inductive F : Type where
  | app : Val → F
  | letin : Com → F

inductive Fₐ : Type where
  | app : ANF.Val → Fₐ
  | letin : ANF.Cfg → Fₐ

@[simp]
def FK : List F → K
  | [] => .nil
  | .app v :: fs => .app (⟦ v ⟧ᵥ) (FK fs)
  | .letin m :: fs => .letin (⟦ m ⟧ₘ renameK succ (FK fs))

@[simp]
def KFₐ : K → List Fₐ
  | .nil => []
  | .app v k => .app v :: KFₐ k
  | .letin m => [.letin m]

@[simp]
def renameF (ξ : Nat → Nat) : List F → List F
  | [] => []
  | .app v :: fs => .app (renameVal ξ v) :: renameF ξ fs
  | .letin m :: fs => .letin (renameCom (lift ξ) m) :: renameF ξ fs

@[simp]
def renameFₐ (ξ : Nat → Nat) : List Fₐ → List Fₐ
  | [] => []
  | .app v :: fs => .app (ANF.renameVal ξ v) :: renameFₐ ξ fs
  | .letin m :: fs => .letin (ANF.renameCfg (lift ξ) m) :: renameFₐ ξ fs

theorem renameFK {fs} (ξ : Nat → Nat) : FK (renameF ξ fs) = renameK ξ (FK fs) := by
  induction fs
  case nil => simp
  case cons f _ ih =>
    cases f <;> simp [-lift]
    case app => exact ⟨renameAval, ih⟩
    case letin => rw [ih, renameKLiftSucc, renameAcom]

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

theorem aeval.aevals {acek acek'} (r : acek ⤳ₐ acek'): acek ⤳ₐ⋆ acek' := .trans r .refl

theorem aevals.trans' {acek₁ acek₂ acek₃} (r : acek₁ ⤳ₐ⋆ acek₂) (r' : acek₂ ⤳ₐ⋆ acek₃) : acek₁ ⤳ₐ⋆ acek₃ := by
  induction r
  case refl => assumption
  case trans => constructor <;> apply_rules

instance : Trans aevals aevals aevals where
  trans := .trans'

theorem equivalence {m m' σ σ' fs fs'} (r : ⟨m, σ, fs⟩ ⤳ ⟨m', σ', fs'⟩) :
  ∀ fsₐ, ∃ fsₐ', ⟨⟦ m ⟧ₘ (FK fs), ⟦ σ ⟧ₛ, fsₐ⟩ ⤳ₐ⋆ ⟨⟦ m' ⟧ₘ (FK fs'), ⟦ σ' ⟧ₛ, fsₐ'⟩ := by
  intro fsₐ
  generalize e : (m, σ, fs) = cek, e' : (m', σ', fs') = cek' at r
  induction r
  all_goals injection e with em e; injection e with eσ ef; subst em eσ ef
  all_goals injection e' with em' e'; injection e' with eσ' ef'; subst em' eσ' ef'
  case force => simp; exists fsₐ; sorry
  case force' => simp; exists fsₐ; sorry
  case lam => rw [Acons]; simp; exists renameFₐ succ fsₐ; sorry
  case app => exact ⟨_, .refl⟩
  case ret v => rw [Acons, renameFK]; exact ⟨_, .trans .letin (.trans .ret .refl)⟩
  case letin => simp; exists fsₐ; exact .refl
  case case₁ => rw [Acons, renameFK]; exact ⟨_, .trans .case₁ .refl⟩
  case case₂ => rw [Acons, renameFK]; exact ⟨_, .trans .case₂ .refl⟩
  case case' => exact ⟨_, aeval.case'.aevals⟩
