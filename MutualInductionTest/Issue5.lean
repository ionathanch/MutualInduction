import MutualInduction
import Joint

inductive Dep : Nat → Nat → Type where
  | mk (n m : Nat) : Dep n m

mutual
inductive Even : Nat → Type where
  | zero : Even 0
  | succ : ∀ n, Odd n → Even (n + 1)

inductive Odd : Nat → Type where
  | succ : ∀ n, Even n → Odd (n + 1)
end

-- `h` is shared by both theorem goals.
-- It is present in all goals, but it still depends on the target index `n`.
-- `m` is also shared by both theorem goals, but it doesn't depend on `n`.
-- Therefore, `h` must be generalized, while `m` need not be.
joint (n m : Nat) (h : Dep n m)
  theorem even_ok (e : Even n) : m = m
  theorem odd_ok  (o : Odd n) : m = m
by
  mutual_induction e, o
  case even_ok.zero =>
    guard_hyp h : Dep 0 m
    trivial
  case even_ok.succ n o ih =>
    guard_hyp h : Dep (n + 1) m
    guard_hyp ih : ∀ (h : Dep n m), m = m
    trivial
  case odd_ok.succ n e ih =>
    guard_hyp h : Dep (n + 1) m
    guard_hyp ih : ∀ (h : Dep n m), m = m
    trivial
