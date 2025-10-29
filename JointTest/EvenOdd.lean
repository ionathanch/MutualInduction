import MutualInduction
import Joint

mutual
inductive Even : Nat → Prop where
  | zero : Even 0
  | succ n : Odd n → Even (n + 1)

inductive Odd : Nat → Prop where
  | succ n : Even n → Odd (n + 1)
end
open Even Odd

/-
  Recursors generated for Even and Odd:

  Even.rec :
    ∀ {motive_1 : ∀ n, Even n → Prop}
      {motive_2 : ∀ n, Odd n → Prop},
    motive_1 0 zero →
    (∀ n (on : Odd n),  motive_2 n on → motive_1 (n + 1) (succ n on)) →
    (∀ n (en : Even n), motive_1 n en → motive_1 (n + 1) (succ n en)) →
    ∀ {n} (en : Even n), motive_1 n en

  Odd.rec :
    ∀ {motive_1 : ∀ n, Even n → Prop}
      {motive_2 : ∀ n, Odd n → Prop},
    motive_1 0 zero →
    (∀ n (on : Odd n),  motive_2 n on → motive_1 (n + 1) (succ n on)) →
    (∀ n (en : Even n), motive_1 n en → motive_1 (n + 1) (succ n en)) →
    ∀ {n} (on : Odd n), motive_2 n on
-/

theorem evenOddInd
  -- motives
  (P : ∀ {n}, Even n → Prop)
  (Q : ∀ {n}, Odd n → Prop)
  -- subgoals
  (ezero : P zero)
  (esucc : ∀ n (on : Odd n), Q on → P (succ n on))
  (osucc : ∀ n (en : Even n), P en → Q (succ n en)) :
  -- goal
  ∀ n, (∀ (en : Even n), P en) ∧ (∀ (on : Odd n), Q on) := by
  intros n; constructor
  case' left  => intro en -- apply @Even.rec @P @Q <;> assumption
  case' right => intro on -- apply @Odd.rec  @P @Q <;> assumption
  mutual_induction on, en
  all_goals apply_rules

theorem evenOddInd'
  -- motives
  (P : ∀ {n}, Even n → Prop)
  (Q : ∀ {n}, Odd n → Prop)
  -- subgoals
  (ezero : P zero)
  (esucc : ∀ n (on : Odd n), Q on → P (succ n on))
  (osucc : ∀ n (en : Even n), P en → Q (succ n en)) :
  -- goal
  ∀ n, (∀ (en : Even n), P en) ∧ (∀ (on : Odd n), Q on) := by
  intro n; induction n
  case' succ ih => let ⟨ihe, iho⟩ := ih
  all_goals constructor <;> intro h <;> cases h <;> apply_rules

joint (n : Nat)
  theorem evenInv (h : Even (n + 1)) : Odd n
  theorem oddInv  (h : Odd  (n + 1)) : Even n
by
  all_goals generalize e : n + 1 = m at h
  mutual_induction h, h
  case zero => injection e
  all_goals injection e with e; subst e; assumption

joint {n m : Nat}
  theorem plusEven (enm : Even (n + m)) : (Even n ∧ Even m) ∨ (Odd n ∧ Odd m)
  theorem plusOdd  (onm : Odd (n + m))  : (Odd n ∧ Even m) ∨ (Even n ∧ Odd m)
by
  case' plusOdd  => generalize e₂ : n + m = k₂ at onm
  case' plusEven => generalize e₁ : n + m = k₁ at enm
  mutual_induction enm, onm generalizing n
  case plusEven.zero =>
    have _ : n = 0 := by omega
    have _ : m = 0 := by omega
    subst n m
    left; constructor <;> constructor
  case plusEven.succ =>
    cases n
    case zero =>
      simp at e₁; subst e₁
      left; constructor <;> constructor; assumption
    case succ k _ ih n =>
      have e : n + m = k := by omega
      cases ih e
      case inl h =>
        let ⟨en, om⟩ := h
        left; constructor; constructor; assumption; assumption
      case inr h =>
        let ⟨en, om⟩ := h
        right; constructor; constructor; assumption; assumption
  case plusOdd.succ =>
    cases n
    case zero =>
      simp at e₂; subst e₂
      right; constructor <;> constructor; assumption
    case succ k _ ih n =>
      have e : n + m = k := by omega
      cases ih e
      case inl h =>
        let ⟨en, om⟩ := h
        left; constructor; constructor; assumption; assumption
      case inr h =>
        let ⟨en, om⟩ := h
        right; constructor; constructor; assumption; assumption

theorem even2 n (en : Even (n + 2)) : Even n := by
  generalize e : n + 2 = m at en
  mutual_induction en generalizing n
  case zero => injection e
  case succ on => cases e; cases on; assumption

mutual
variable
  {motive_1 : ∀ n, Even n → Prop}
  {motive_2 : ∀ n, Odd n → Prop}

inductive Even.below' : ∀ {n}, Even n → Prop where
  | zero : Even.below' zero
  | succ : ∀ n {on : Odd n}, motive_2 n on →
    Odd.below' on → Even.below' (succ n on)

inductive Odd.below' : ∀ {n}, Odd n → Prop where
  | succ : ∀ n {en : Even n}, motive_1 n en →
    Even.below' en → Odd.below' (succ n en)
end

joint
  {P : ∀ n, Even n → Prop} {Q : ∀ n, Odd  n → Prop} {n : Nat}
  (he : ∀ {n} {en : Even n}, @Even.below P Q n en → P n en)
  (ho : ∀ {n} {on : Odd  n}, @Odd.below  P Q n on → Q n on)
  theorem Even.brecOn' : ∀ (en : Even n), P n en
  theorem Odd.brecOn'  : ∀ (on : Odd  n), Q n on
by
  case' Odd.brecOn'  => intro on; apply ho
  case' Even.brecOn' => intro en; apply he
  mutual_induction en, on using Even.rec, Odd.rec
  case zero => exact Even.below.zero
  case Even.brecOn'.succ ih => exact Even.below.succ _ _ ih (ho ih)
  case Odd.brecOn'.succ  ih => exact Odd.below.succ  _ _ ih (he ih)
