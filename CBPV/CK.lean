import CBPV.RTC
import CBPV.Syntax
import CBPV.Evaluation

open Val Com

namespace CK

inductive F : Type where
  | app : Val → F
  | letin : Com → F
  | fst : F
  | snd : F
open F

def K := List F
def CK := Com × K

@[simp]
def renameK (ξ : Nat → Nat) : K → K
  | [] => []
  | .app v :: k => app (renameVal ξ v) :: renameK ξ k
  | .letin m :: k => letin (renameCom (lift ξ) m) :: renameK ξ k
  | .fst :: k => fst :: renameK ξ k
  | .snd :: k => snd :: renameK ξ k

@[simp]
def dismantle (n : Com) : K → Com
  | [] => n
  | .app v :: k => dismantle (app n v) k
  | .letin m :: k => dismantle (letin n m) k
  | .fst :: k => dismantle (fst n) k
  | .snd :: k => dismantle (snd n) k

section
set_option hygiene false
local infix:40 "⤳" => Step
inductive Step : CK → CK → Prop where
  | β {m v k} :     ⟨lam m, app v :: k⟩   ⤳ ⟨substCom (v +: var) m, k⟩
  | ζ {v m k} :     ⟨ret v, letin m :: k⟩ ⤳ ⟨substCom (v +: var) m, k⟩
  | ιl {v m n k} :  ⟨case (inl v) m n, k⟩ ⤳ ⟨substCom (v +: var) m, k⟩
  | ιr {v m n k} :  ⟨case (inr v) m n, k⟩ ⤳ ⟨substCom (v +: var) n, k⟩
  | π {m k} :       ⟨force (thunk m), k⟩  ⤳ ⟨m, k⟩
  | π1 {m n k} :    ⟨prod m n, fst :: k⟩  ⤳ ⟨m, k⟩
  | π2 {m n k} :    ⟨prod m n, snd :: k⟩  ⤳ ⟨n, k⟩
  | app {m v k} :   ⟨app m v, k⟩          ⤳ ⟨m, app v :: k⟩
  | letin {m n k} : ⟨letin m n, k⟩        ⤳ ⟨m, letin n :: k⟩
  | fst {m k} :     ⟨fst m, k⟩            ⤳ ⟨m, fst :: k⟩
  | snd {m k} :     ⟨snd m, k⟩            ⤳ ⟨m, snd :: k⟩
end
infix:40 "⤳" => Step

@[reducible] def Steps := RTC Step
infix:40 "⤳⋆"  => Steps

end CK

namespace Big

section
set_option hygiene false
local infix:40 "⇓" => BStep
inductive BStep : Com → Com → Prop where
  | lam {m} : lam m ⇓ lam m
  | ret {v} : ret v ⇓ ret v
  | prod {m₁ m₂} : prod m₁ m₂ ⇓ prod m₁ m₂
  | π {m t} :
    m ⇓ t →
    -------------------
    force (thunk m) ⇓ t
  | β {n t m v} :
    n ⇓ lam m →
    substCom (v +: var) m ⇓ t →
    ---------------------------
    app n v ⇓ t
  | ζ {n t v m} :
    n ⇓ ret v →
    substCom (v +: var) m ⇓ t →
    ---------------------------
    letin n m ⇓ t
  | ιl {v m₁ m₂ t}:
    substCom (v +: var) m₁ ⇓ t →
    ----------------------------
    case (inl v) m₁ m₂ ⇓ t
  | ιr {v m₁ m₂ t}:
    substCom (v +: var) m₂ ⇓ t →
    ----------------------------
    case (inr v) m₁ m₂ ⇓ t
  | π1 {n t m₁ m₂} :
    n ⇓ prod m₁ m₂ →
    m₁ ⇓ t →
    ----------------
    fst n ⇓ t
  | π2 {n t m₁ m₂} :
    n ⇓ prod m₁ m₂ →
    m₂ ⇓ t →
    ----------------
    snd n ⇓ t
end
infix:40 "⇓" => BStep

end Big

namespace Eq

section
set_option hygiene false
local infix:40 "≡" => EqVal
local infix:40 "≡" => EqCom
mutual
inductive EqVal : Val → Val → Prop
  | var {x} : var x ≡ var x
  | unit : unit ≡ unit
  | inl {v w : Val} : v ≡ w → inl v ≡ inl w
  | inr {v w : Val} : v ≡ w → inr v ≡ inr w
  | thunk {m n : Com} : m ≡ n → thunk m ≡ thunk n
  | sym {v w : Val} : w ≡ v → v ≡ w
  | trans {u v w : Val} : u ≡ v → v ≡ w → u ≡ w

inductive EqCom : Com → Com → Prop
  | force {v w : Val} : v ≡ w → force v ≡ force w
  | lam {m n : Com} : m ≡ n → lam m ≡ lam n
  | app {m n : Com} {v w : Val} : m ≡ n → v ≡ w → app m v ≡ app n w
  | ret {v w : Val} : v ≡ w → ret v ≡ ret w
  | letin {n₁ n₂ m₁ m₂ : Com} : m₁ ≡ n₁ → m₂ ≡ n₂ → letin m₁ m₂ ≡ letin n₁ n₂
  | case {v w : Val} {m₁ n₁ m₂ n₂ : Com} : v ≡ w → m₁ ≡ n₁ → m₂ ≡ n₂ → case v m₁ m₂ ≡ case w n₁ n₂
  | prod {m₁ m₂ n₁ n₂ : Com} : m₁ ≡ n₁ → m₂ ≡ n₂ → prod m₁ m₂ ≡ prod n₁ n₂
  | fst {m n : Com} : m ≡ n → fst m ≡ fst n
  | snd {m n : Com} : m ≡ n → snd m ≡ snd n
  | β {m v} : app (lam m) v ≡ m⦃v⦄
  | ζ {m v} : letin (ret v) m ≡ m⦃v⦄
  | ιl {v m₁ m₂} : case (inl v) m₁ m₂ ≡ m₁⦃v⦄
  | ιr {v m₁ m₂} : case (inr v) m₁ m₂ ≡ m₂⦃v⦄
  | π {m} : force (thunk m) ≡ m
  | π1 {m₁ m₂} : fst (prod m₁ m₂) ≡ m₁
  | π2 {m₁ m₂} : snd (prod m₁ m₂) ≡ m₂
  | sym {m n : Com} : n ≡ m → m ≡ n
  | trans {m n p : Com} : m ≡ n → n ≡ p → m ≡ p
end
end
infix:40 "≡" => EqVal
infix:40 "≡" => EqCom

theorem reflValCom :
  (∀ {v : Val}, v ≡ v) ∧
  (∀ {m : Com}, m ≡ m) := by
  refine ⟨λ {v} ↦ ?val, λ {m} ↦ ?com⟩
  mutual_induction v, m
  all_goals constructor <;> assumption

@[refl] theorem EqVal.refl : ∀ {v : Val}, v ≡ v := reflValCom.left
@[refl] theorem EqCom.refl : ∀ {m : Com}, m ≡ m := reflValCom.right

instance : Trans EqCom EqCom EqCom where
  trans := .trans

end Eq

open CK Big

/-* CK machine semantics is sound wrt small-step evaluation semantics *-/

theorem evalCongK {m n k} (r : m ⇒ n) : dismantle m k ⇒ dismantle n k := by
  induction k generalizing m n
  case nil => simp [r]
  case cons f _ ih =>
    cases f
    all_goals apply ih; constructor; apply r

theorem stepEval {m n k₁ k₂} (r : ⟨m, k₁⟩ ⤳ ⟨n, k₂⟩) :
  (dismantle m k₁ ⇒ dismantle n k₂) ∨ (dismantle m k₁ = dismantle n k₂) := by
  generalize e₁ : (m, k₁) = ck₁ at r
  generalize e₂ : (n, k₂) = ck₂ at r
  induction r generalizing m n k₁ k₂
  all_goals injection e₁ with em ek₁; subst em ek₁
  all_goals injection e₂ with en ek₂; subst en ek₂
  case β | ζ | ιl | ιr | π | π1 | π2 => (try simp); left; apply evalCongK; constructor
  case app | letin | fst | snd => right; rfl

theorem stepEvals {m n k₁ k₂} (r : ⟨m, k₁⟩ ⤳⋆ ⟨n, k₂⟩) : dismantle m k₁ ⇒⋆ dismantle n k₂ := by
  generalize e₁ : (m, k₁) = ck₁ at r
  generalize e₂ : (n, k₂) = ck₂ at r
  induction r generalizing m n k₁ k₂
  case refl => subst e₁; injection e₂ with em ek; subst em ek; rfl
  case trans ck _ r _ ih =>
    subst e₁ e₂; cases ck; specialize ih rfl rfl
    match stepEval r with
    | .inl r => exact .trans r ih
    | .inr e => simp [e, ih]

theorem stepEvalsNil {m n} : ⟨m, []⟩ ⤳⋆ ⟨n, []⟩ → m ⇒⋆ n := stepEvals

/-* CK machine semantics is complete wrt big-step semantics *-/

theorem stepBig {m n k} (r : m ⇓ n) : ⟨m, k⟩ ⤳⋆ ⟨n, k⟩ := by
  induction r generalizing k
  case lam | ret | prod => rfl
  case π ih => exact .trans .π ih
  case ιl ih => exact .trans .ιl ih
  case ιr ih => exact .trans .ιr ih
  case β n t m v _ _ ih₁ ih₂ =>
    calc ⟨app n v, k⟩
      _ ⤳  ⟨n, .app v :: k⟩     := .app
      _ ⤳⋆ ⟨lam m, .app v :: k⟩ := ih₁
      _ ⤳  ⟨m⦃v⦄, k⟩            := .β
      _ ⤳⋆ ⟨t, k⟩               := ih₂
  case ζ n t v m _ _ ih₁ ih₂ =>
    calc ⟨letin n m, k⟩
      _ ⤳  ⟨n, .letin m :: k⟩     := .letin
      _ ⤳⋆ ⟨ret v, .letin m :: k⟩ := ih₁
      _ ⤳  ⟨m⦃v⦄, k⟩              := .ζ
      _ ⤳⋆ ⟨t, k⟩                 := ih₂
  case π1 n t m₁ m₂ _ _ ih₁ ih₂ =>
    calc ⟨fst n, k⟩
      _ ⤳  ⟨n, .fst :: k⟩          := .fst
      _ ⤳⋆ ⟨prod m₁ m₂, .fst :: k⟩ := ih₁
      _ ⤳  ⟨m₁, k⟩                 := .π1
      _ ⤳⋆ ⟨t, k⟩                  := ih₂
  case π2 n t m₁ m₂ _ _ ih₁ ih₂ =>
    calc ⟨snd n, k⟩
      _ ⤳  ⟨n, .snd :: k⟩          := .snd
      _ ⤳⋆ ⟨prod m₁ m₂, .snd :: k⟩ := ih₁
      _ ⤳  ⟨m₂, k⟩                 := .π2
      _ ⤳⋆ ⟨t, k⟩                  := ih₂

/-* CK machine is complete wrt small-step evaluation via big-step *-/

theorem evalBig {m n t} (r : m ⇒ n) : n ⇓ t → m ⇓ t := by
  induction r generalizing t <;> intro r
  case π => exact .π r
  case β => exact .β .lam r
  case ζ => exact .ζ .ret r
  case ιl => exact .ιl r
  case ιr => exact .ιr r
  case π1 => exact .π1 .prod r
  case π2 => exact .π2 .prod r
  case app ih =>
    cases r with | β r₁ r₂ => exact .β (ih r₁) r₂
  case letin ih =>
    cases r with | ζ r₁ r₂ => exact .ζ (ih r₁) r₂
  case fst ih =>
    cases r with | π1 r₁ r₂ => exact .π1 (ih r₁) r₂
  case snd ih =>
    cases r with | π2 r₁ r₂ => exact .π2 (ih r₁) r₂

theorem evalBigs {m n t} (r : m ⇒⋆ n) : n ⇓ t → m ⇓ t := by
  induction r generalizing t <;> intro r
  case refl => exact r
  case trans r' _ ih => exact evalBig r' (ih r)

theorem bigNf {t} (nt : nf t) : t ⇓ t := by
  mutual_induction t generalizing nt
  all_goals simp at nt
  all_goals constructor

theorem evalStep {m t} (nt : nf t) (r : m ⇒⋆ t) : ⟨m, []⟩ ⤳⋆ ⟨t, []⟩ :=
  stepBig (evalBigs r (bigNf nt))

/-* CK machine is sound wrt equational theory *-/

theorem eqCongK {m n : Com} {k} (e : m ≡ n) : dismantle m k ≡ dismantle n k := by
  induction k generalizing m n
  case nil => simp [e]
  case cons f _ ih =>
    cases f <;> (apply ih; constructor)
    all_goals first | assumption | rfl

theorem stepEq {m n k₁ k₂} (r : ⟨m, k₁⟩ ⤳ ⟨n, k₂⟩) : dismantle m k₁ ≡ dismantle n k₂ := by
  cases r
  case app | letin | fst | snd => rfl
  all_goals (try simp); apply eqCongK; constructor

theorem stepsEq {m n k₁ k₂} (r : ⟨m, k₁⟩ ⤳⋆ ⟨n, k₂⟩) : dismantle m k₁ ≡ dismantle n k₂ := by
  generalize e₁ : (m, k₁) = ck₁ at r
  generalize e₂ : (n, k₂) = ck₂ at r
  induction r generalizing m n k₁ k₂
  case refl => subst e₁; injection e₂ with em ek; subst em ek; rfl
  case trans ck _ r _ ih => subst e₁ e₂; exact .trans (stepEq r) (ih rfl rfl)

theorem stepsEqNil {m n} (r : ⟨m, []⟩ ⤳⋆ ⟨n, []⟩) : m ≡ n := stepsEq r
