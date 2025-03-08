import «MutualInduction».MutualInduction

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
  mutual_induction | right => on | left => en
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
  mutual_induction | left => h | right => h
  case zero => injection e
  all_goals injection e with e; subst e; assumption

theorem evenOddInv' (n : Nat) :
  (∀ m, m = n + 1 → Even m → Odd n) ∧
  (∀ m, m = n + 1 → Odd  m → Even n) := by
  constructor
  all_goals intro m e h
  mutual_induction | left => h | right => h
  case zero => injection e
  all_goals injection e with e; subst e; assumption
