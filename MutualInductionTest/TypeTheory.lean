import MutualInduction

inductive Term : Type where
  | var : Nat → Term
  | type : Term
  | arr : Term → Term → Term
  | abs : Term → Term
  | app : Term → Term → Term

inductive Ctxt : Type where
  | nil : Ctxt
  | cons : Ctxt → Term → Ctxt
notation:50 "⬝" => Ctxt.nil
infixl:50 "∷" => Ctxt.cons

axiom subst : Term → Term → Term
axiom In : Nat → Term → Ctxt → Prop
axiom Eqv : Term → Term → Prop
axiom refl : ∀ {a}, Eqv a a
axiom trans : ∀ {a b c}, Eqv a b → Eqv b c → Eqv a c
notation:40 Γ:41 "∋" x:41 "∶" A:41 => In x A Γ
notation:40 a:41 "≡" b:41 => Eqv a b

section
set_option hygiene false
local notation:40 "⊢" Γ:40 => Wf Γ
local notation:40 Γ:41 "⊢" a:41 "∶" A:41 => Wt Γ a A
open Term

mutual
-- ⊢ Γ
inductive Wf : Ctxt → Prop where
  | nil : ⊢ ⬝
  | cons {Γ A} :
    ⊢ Γ →
    Γ ⊢ A ∶ type →
    ---------------
    ⊢ Γ ∷ A

-- Γ ⊢ a ∶ A
inductive Wt : Ctxt → Term → Term → Prop where
  | var {Γ x A} :
    Γ ∋ x ∶ A →
    ⊢ Γ →
    ---------------
    Γ ⊢ var x ∶ A
  | type {Γ} :
    ⊢ Γ →
    -----------------
    Γ ⊢ type ∶ type
  | arr {Γ A B} :
    Γ ⊢ A ∶ type →
    Γ ∷ A ⊢ B ∶ type →
    --------------------
    Γ ⊢ arr A B ∶ type
  | abs {Γ b A B} :
    Γ ⊢ A ∶ type →
    Γ ∷ A ⊢ b ∶ B →
    ---------------------
    Γ ⊢ abs b ∶ arr A B
  | app {Γ b a A B} :
    Γ ⊢ b ∶ arr A B →
    Γ ⊢ a ∶ A →
    ------------------------
    Γ ⊢ app b a ∶ subst B a
  | conv {Γ a A B} :
    Γ ⊢ a ∶ A →
    Γ ⊢ B ∶ type →
    A ≡ B →
    ---------------
    Γ ⊢ a ∶ B
end
end

notation:40 "⊢" Γ:40 => Wf Γ
notation:40 Γ:41 "⊢" a:41 "∶" A:41 => Wt Γ a A
open Wf Wt

/-
  Recursors generated for ⊢ Γ and Γ ⊢ a ∶ A:

  Wf.rec :
    ∀ {motive_1 : ∀ Γ, ⊢ Γ → Prop}
      {motive_2 : ∀ Γ a A, Γ ⊢ a ∶ A → Prop},
    ... Wf cases ...
    (∀ {Γ x a A} (mem : Γ ∋ x ∶ A) (h : ⊢ Γ),
       motive_1 Γ h →
       motive_2 Γ (.var x) A (Wt.var mem h)) →
    ... other Wt cases ...
    ∀ {Γ} (h : ⊢ Γ), motive_1 Γ h

  Wt.rec :
    ∀ {motive_1 : ∀ Γ, ⊢ Γ → Prop}
      {motive_2 : ∀ Γ a A, Γ ⊢ a ∶ A → Prop},
    ... cases ...
    ∀ {Γ a A} (h : Γ ⊢ a ∶ A), motive_2 Γ a A h
-/

theorem wtfInd
  -- motives
  (Q : ∀ {Γ}, ⊢ Γ → Prop)
  (P : ∀ {Γ a A}, Γ ⊢ a ∶ A → Prop)
  -- Wf subgoals
  (nil : Q nil)
  (cons : ∀ {Γ A}
    (h : ⊢ Γ)
    (hA : Γ ⊢ A ∶ .type),
    Q h → P hA → Q (cons h hA))
  -- Wt subgoals
  (var : ∀ {Γ x A}
    (mem : Γ ∋ x ∶ A)
    (h : ⊢ Γ),
    Q h → P (var mem h))
  (type : ∀ {Γ}
    (h : ⊢ Γ),
    Q h → P (type h))
  (arr : ∀ {Γ A B}
    (hA : Γ ⊢ A ∶ .type)
    (hB : Γ ∷ A ⊢ B ∶ .type),
    P hA → P hB → P (arr hA hB))
  (abs : ∀ {Γ b A B}
    (hA : Γ ⊢ A ∶ .type)
    (hb : Γ ∷ A ⊢ b ∶ B),
    P hA → P hb → P (abs hA hb))
  (app : ∀ {Γ b a A B}
    (hb : Γ ⊢ b ∶ .arr A B)
    (ha : Γ ⊢ a ∶ A),
    P hb → P ha → P (app hb ha))
  (conv : ∀ {Γ a A B}
    (ha : Γ ⊢ a ∶ A)
    (hB : Γ ⊢ B ∶ .type)
    (e : A ≡ B),
    P ha → P hB → P (conv ha hB e))
  -- goal
  : (∀ {Γ} (h : ⊢ Γ), Q h) ∧ (∀ {Γ a A} (h : Γ ⊢ a ∶ A), P h) := by
  constructor
  case' left => intro Γ h
  case' right => intro Γ a A h
  mutual_induction | left => h | right => h
  case nil  => exact nil
  case cons => apply cons <;> assumption
  case var  => apply var  <;> assumption
  case type => apply type <;> assumption
  case arr  => apply arr  <;> assumption
  case abs  => apply abs  <;> assumption
  case app  => apply app  <;> assumption
  case conv => apply conv <;> assumption

def wtInd P := @Wt.rec (λ _ _ ↦ True) P (by simp) (by simp)

def wfInd (P : ∀ {Γ}, ⊢ Γ → Prop)
  (nil : P .nil)
  (cons : ∀ {Γ A} (h : ⊢ Γ) (hA : Γ ⊢ A ∶ .type), P (.cons h hA))
  : ∀ {Γ} (h : ⊢ Γ), P h := by
  apply @Wf.rec @P (λ _ _ _ _ ↦ True) nil
  case cons => intros; apply_rules
  case var | type | arr | abs | app | conv => simp

theorem wtwf {Γ a A} (h : Γ ⊢ a ∶ A) : ⊢ Γ := by
  have _ (h : ⊢ Γ) : True := ?dummy
  mutual_induction | _ => h | dummy => h
  all_goals try simp at * <;> assumption
  -- induction h using Wt.rec (motive_1 := λ _ _ ↦ True)

theorem regularity {Γ} :
  (∀ x A, Γ ∋ x ∶ A → ⊢ Γ → Γ ⊢ A ∶ .type) ∧
  (∀ a A, Γ ⊢ a ∶ A → Γ ⊢ A ∶ .type) := by
  constructor
  case' left => intro x A mem h
  case' right => intro a A h
  mutual_induction | left => h | right => h
  case nil => sorry
  case cons => sorry
  case var mem _ ih => exact ih _ _ mem
  case type => constructor; assumption
  case arr => constructor; apply wtwf; assumption
  case abs => constructor <;> assumption
  case app => sorry
  case conv => assumption
