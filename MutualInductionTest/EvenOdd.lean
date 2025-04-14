import MutualInduction

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

theorem evenOddInv :
  (∀ n m, m = n + 1 → Even m → Odd n) ∧
  (∀ n m, m = n + 1 → Odd  m → Even n) := by
  constructor
  all_goals intro n m e h
  mutual_induction h, h
  case zero => injection e
  all_goals injection e with e; subst e; assumption

theorem evenOddInv' (n : Nat) :
  (∀ m, m = n + 1 → Even m → Odd n) ∧
  (∀ m, m = n + 1 → Odd  m → Even n) := by
  constructor
  all_goals intro m e h
  mutual_induction h, h
  case zero => injection e
  all_goals injection e with e; subst e; assumption

theorem plusEvenOdd n m :
  (Even (n + m) → (Even n ∧ Even m) ∨ (Odd n ∧ Odd m)) ∧
  (Odd (n + m) → (Odd n ∧ Even m) ∨ (Even n ∧ Odd m)) := by
  constructor
  case' right => intro onm; generalize e₂ : n + m = k₂ at onm
  case' left => intro enm; generalize e₁ : n + m = k₁ at enm
  mutual_induction enm, onm generalizing n
  case left.zero =>
    have _ : n = 0 := by omega
    have _ : m = 0 := by omega
    subst n m
    left; constructor <;> constructor
  case left.succ =>
    cases n
    case zero =>
      simp at e₁; subst e₁
      left; constructor <;> constructor; assumption
    case succ k _ ih n =>
      have e : n + m = k := by omega
      cases ih n e
      case inl h =>
        let ⟨en, om⟩ := h
        left; constructor; constructor; assumption; assumption
      case inr h =>
        let ⟨en, om⟩ := h
        right; constructor; constructor; assumption; assumption
  case right.succ =>
    cases n
    case zero =>
      simp at e₂; subst e₂
      right; constructor <;> constructor; assumption
    case succ k _ ih n =>
      have e : n + m = k := by omega
      cases ih n e
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

theorem brecOn
  {P : ∀ n, Even n → Prop}
  {Q : ∀ n, Odd  n → Prop} :
  (∀ {n} {en : Even n}, @Even.below P Q n en → P n en) →
  (∀ {n} {on : Odd  n}, @Odd.below  P Q n on → Q n on) →
  (∀ {n} (en : Even n), P n en) ∧
  (∀ {n} (on : Odd  n), Q n on) := by
  intro he ho
  constructor
  case' left  => intro n en; apply he
  case' right => intro n on; apply ho
  mutual_induction on, en
  case zero => exact Even.below.zero
  case left.succ  ih => exact Even.below.succ _ ih (ho ih)
  case right.succ ih => exact Odd.below.succ  _ ih (he ih)
