# Mutual induction tactic for Lean 4

This is an experimental mutual induction tactic that acts on multiple goals.
For now, the syntax looks like the below,
with no support yet for the usual `induction` tactic's features of
`using`, `generalizing`, or `with`.

```lean
mutual_induction | tag₁ => x₁ ... | tagₙ => xₙ
```

The doc comment for the tactic gives an example using mutual even/odd naturals,
which demonstrates basic usage but not some of the subtler issues with implementation.
Here, we'll use even/odd predicates over naturals as the running example.

```lean
mutual
inductive Even : Nat → Prop
  | zero : Even 0
  | succ : ∀ n, Odd n → Even (n + 1)
inductive Odd : Nat → Prop
  | succ : ∀ n, Even n → Odd (n + 1)
end
open Even Odd
```

## Mutual induction with recursors

Recursors are generated for this mutual pair of inductives,
which share the same motives and cases but with different conclusions.

```lean
Even.rec : ∀ {motive_1 : ∀ n, Even n → Prop} {motive_2 : ∀ n, Odd n → Prop},
  -- cases for Even
  motive_1 0 zero →
  (∀ n (on : Odd n),  motive_2 n on → motive_1 (n + 1) (succ n on)) →
  -- cases for Odd
  (∀ n (en : Even n), motive_1 n en → motive_2 (n + 1) (succ n en)) →
  -- conclusion for Even
  ∀ {n} (en : Even n), motive_1 n en

Odd.rec  : ∀ {motive_1 : ∀ n, Even n → Prop} {motive_2 : ∀ n, Odd n → Prop},
  -- cases for Even
  motive_1 0 zero →
  (∀ n (on : Odd n),  motive_2 n on → motive_1 (n + 1) (succ n on)) →
  -- cases for Odd
  (∀ n (en : Even n), motive_1 n en → motive_2 (n + 1) (succ n en)) →
  -- conclusion for Odd
  ∀ {n} (on : Odd n), motive_2 n on
```

We can conjoin the two conclusions into a single recursor using these two
to avoid duplicating work proving the identical cases.

```lean
theorem rec : ∀ {motive_1 motive_2}, ... →
  (∀ {n} (en : Even n), motive_1 n en) ∧
  (∀ {n} (on : Odd n),  motive_2 n on) := by ...
```

The disadvantage of using the conjoined recursor
is that the goal must have exactly this shape
for unification to solve goals automatically.
Otherwise, it must be manually applied and manipulated.
For example, reordering and pulling the `n` out of the conjunction is equivalent:

```lean
theorem rec' : ∀ {motive_1 motive_2}, ... → ∀ {n},
  (∀ (on : Odd n),  motive_2 n on) ∧
  (∀ (en : Even n), motive_1 n en) := by ...
```

but one cannot be proven from the other without destructing a conjunction
along with additional instantiations or introductions.

## Mutual induction with the tactic

The aim of this mutual induction tactic is to alleviate this manipulation tedium
by avoiding conjunctions altogether.
To demonstrate, we prove an inversion theorem about parity addition:
if the addition of two naturals is even, then they are either both even or both odd;
and if the addition of two naturals is odd, then one must be even and the other odd.

```lean
theorem plusEvenOdd m :
  (∀ n, Even (n + m) → (Even n ∧ Even m) ∨ (Odd  n ∧ Odd m)) ∧
  (∀ n, Odd  (n + m) → (Odd  n ∧ Even m) ∨ (Even n ∧ Odd m)) := by
  constructor
  case' left  => intro n enm; generalize e : n + m = k at enm
  case' right => intro n onm; generalize e : n + m = k at onm
```

We wish induct on the proofs of `Even (n + m)` and `Odd (n + m)`.
Just as with the usual `induction` tactic,
we can't induct on inductives whose indices aren't variables,
so we generalize `n + m` over an equality.
The proof state now looks like the below.

```lean
▼ case left
m n₁ k₁ : Nat
e₁ : n₁ + m = k₁
enm : Even k₁
⊢ (Even n₁ ∧ Even m) ∨ (Odd n₁ ∧ Odd m)

▼ case right
m n₂ k₂ : Nat
e₂ : n₂ + m = k₂
onm : Odd k₂
⊢ (Odd n₂ ∧ Even m) ∨ (Even n₂ ∧ Odd m)
```

We now apply mutual induction by `mutual_induction | left => enm | right => onm`,
which says that we are doing induction on `enm` in goal `left` and on `onm` in goal `right`.
It yields the following goals.

```lean
▼ case left.zero
m n₁ : Nat
e₁ : n₁ + m = 0
⊢ (Even n₁ ∧ Even m) ∨ (Odd n₁ ∧ Odd m)

▼ case left.succ
m k₁ : Nat
ok : Odd k₁
ih : ∀ (n : Nat), n + m = k₁ → (Odd n ∧ Even m) ∨ (Even n ∧ Odd m)
n₁ : Nat
e₁ : n₁ + m = k₁ + 1
⊢ (Even n₁ ∧ Even m) ∨ (Odd n₁ ∧ Odd m)

▼ case right.succ
m k₂ : Nat
ek : Even k₂
ih : ∀ (n : Nat), n + m = k₂ → Even n ∧ Even m ∨ Odd n ∧ Odd m
n₂ : Nat
e₂ : n₂ + m = k₂ + 1
⊢ (Odd n₂ ∧ Even m) ∨ (Even n₂ ∧ Odd m)
```

The proof proceeds by cases on `n` in the `succ` cases,
which is why we need the induction hypothesis to be generalized over it.
The full proof can be found at `EvenOdd.plusEvenOdd`.

## How does the tactic work?

The tactic proceeds in five stages:

1. Compute whatever information we can from each goal independently.
2. Ensure that the goals match the mutual inductives.
3. Compute more information from all goals in tandem.
4. Apply the appropriate recursor for each goal.
5. Combine duplicate subgoals from the recursors.

### 1. Compute targets and generalized variables

The user specifies that the target of `left` is `enm` and the target of `right` is `onm`.
However, the indices of their types are considered as auxiliary targets
because the motives need to abstract over them as well.
This would be `k₁` and `k₂` in their respective goals.

We also retrieve the inductive type to which the primary target belongs,
along with the positions of the motive for that inductive type and of the targets
within the type of the recursor for that inductive type.
These are `Even`, `[0, 5, 6]` for the first goal,
and `Odd`, `[1, 5, 6]` for the second.

Now, we need to find the variables to generalize the goals over, which are

1. The variables whose types depend on the targets; but also
2. In the types of *those* variables, the other variables they depend on; and
3. The other variables that the goal depends on.

The variables in bucket (1) are what get generalized in the usual `induction` tactic.
However, because we are dealing with multiple goals in different contexts,
we need to ensure when we turn the goals into motives that they are closed,
which means possibly generalizing over all variables in buckets (2) and (3).
In our example, this corresponds to

* (1) `e₁` and `e₂` by dependency on auxiliary targets `k₁` and `k₂`, respectively;
* (2, 3) `m`, `n₁`, and `n₂`, depended upon by `e₁`, `e₂`, and the goals.

This work is done by `Lean.Elab.Tactic.getSubgoal`.

### 2. Check coverage

[TODO]

This work is done by `Lean.Elab.Tactic.checkTargets`.

### 3. Generalize variables and compute motives

Although we compute the variables that may be generalized independently for each goal,
we don't yet actually generalize them,
because there may variables that happen to be common to all goals
that don't need to be generalized over because they'll always be in scope.
In this case, `m` is the only such variable,
which makes sense because it was introduced outside of the conjunction.
Only now do we finally generalize the variables
and compute the motives by abstracting the goals over the targets.

```lean
▼ case left
m k₁ : Nat
enm : Even k₁
motive_1 := λ (k₁ : Nat) (enm : Even k₁) ↦
  ∀ (n₁ : Nat) (e₁ : n₁ + m = 0), (Even n ∧ Even m₁) ∨ (Odd n ∧ Odd m₁)
⊢ ∀ (n₁ : Nat) (e₁ : n₁ + m = 0), (Even n ∧ Even m₁) ∨ (Odd n ∧ Odd m₁)

▼ case right
m k₂ : Nat
onm : Odd k₂
motive_2 := λ (k₂ : Nat) (onm : Odd k₂) ↦
  ∀ (n₂ : Nat) (e₂ : n₂ + m = 0), (Odd n ∧ Even m₂) ∨ (Even n ∧ Odd m₂)
⊢ ∀ (n₂ : Nat) (e₂ : n₂ + m = 0), (Odd n ∧ Even m₂) ∨ (Even n ∧ Odd m₂)
```

For each goal, we know the position of the motive that applies to its target
within the type of the recursor to apply,
but not the positions of the other motives.
Therefore, we assume that all recursors take all motives in exactly the same order,
which is true of the autogenerated recursors,
and sort the motives in that order.
This makes it a point of failure if we later implement the `using` extension
and allow providing the motives in arbitrary order.

This work is done by `Lean.Elab.Tactics.addMotives`.

### 4. Apply recursors

In each goal, we know the primary target and its inductive type,
so we can retrieve the recursor for that inductive type
and instantiate it with the motives and targets,
leaving the remaining arguments as subgoals to be solved.

```lean
▼ case left
m k₁ : Nat
enm : Even k₁
motive_1 := λ (k₁ : Nat) (enm : Even k₁) ↦
  ∀ (n₁ : Nat) (e₁ : n₁ + m = 0), (Even n ∧ Even m₁) ∨ (Odd n ∧ Odd m₁)
motive_2 := λ (k₂ : Nat) (onm : Odd k₂) ↦
  ∀ (n₂ : Nat) (e₂ : n₂ + m = 0), (Odd n ∧ Even m₂) ∨ (Even n ∧ Odd m₂)
⊢ @Even.rec motive_1 motive_2 ?left.Even.zero ?left.Even.succ ?left.Odd.succ k₁ enm
  : ∀ (n₁ : Nat) (e₁ : n₁ + m = 0), (Even n₁ ∧ Even m) ∨ (Odd n₁ ∧ Odd m)

▼ case right
m k₂ : Nat
onm : Odd k₂
motive_1 := λ (k₁ : Nat) (enm : Even k₁) ↦
  ∀ (n₁ : Nat) (e₁ : n₁ + m = 0), (Even n ∧ Even m₁) ∨ (Odd n ∧ Odd m₁)
motive_2 := λ (k₂ : Nat) (onm : Odd k₂) ↦
  ∀ (n₂ : Nat) (e₂ : n₂ + m = 0), (Odd n ∧ Even m₂) ∨ (Even n ∧ Odd m₂)
⊢ @Odd.rec motive_1 motive_2 ?right.Even.zero ?right.Even.succ ?right.Odd.succ k₁ enm
  : ∀ (n₂ : Nat) (e₂ : n₂ + m = 0), (Odd n₂ ∧ Even m) ∨ (Even n₂ ∧ Odd m)
```

The subgoals are collected up as a 2D array.

```lean4
[[?left.Even.zero,  ?left.Even.succ,  ?left.Odd.succ],
 [?right.Even.zero, ?right.Even.succ, ?right.Odd.succ]]
```

This work is done by `Lean.Elab.Tactic.evalSubgoal`.

### 5. Deduplicate subgoals

By virtue of the types of the recursors,
the arrays of subgoals have the same type pointwise,
so we can pick one from each array and equate the rest to it.
These subgoals each correspond to one of the constructors of the mutual inductive types.
We intuitively expect the prefix of the name of the subgoal for a particular constructor
to match the original goal whose target's inductive type contains that constructor.
Picking the subgoals that prove the motive that applies to the parent goal's target
ensures that we get the correct name.

```lean
▼ case left.Even.zero
m : Nat
⊢ ∀ (n₁ : Nat) (e₁ : n₁ + m = 0), (Even n₁ ∧ Even m) ∨ (Odd n₁ ∧ Odd m)

▼ case left.Even.succ
m : Nat
⊢ ∀ (k₁ : Nat) (enm : Even k₁),
  (∀ (n : Nat), n + m = k₁ → (Odd n ∧ Even m) ∨ (Even n ∧ Odd m)) →
  ∀ (n₁ : Nat) (e₁ : n₁ + m = k₁ + 1), (Even n₁ ∧ Even m) ∨ (Odd n₁ ∧ Odd m)

▼ case right.Odd.succ
m : Nat
⊢ ∀ (k₁ : Nat) (enm : Even k₁),
  (∀ (n : Nat), n + m = k₂ → Even n ∧ Even m ∨ Odd n ∧ Odd m) →
  ∀ (n₂ : Nat) (e₂ : n₂ + m = k₂ + 1), (Odd n₂ ∧ Even m) ∨ (Even n₂ ∧ Odd m)

▶ case right.Even.zero := left.Even.zero
▶ case right.Even.succ := left.Even.succ
▶ case left.Odd.succ   := right.Odd.succ
```

To clean up, we remove the name of the inductive type from the goal,
then intros the constructor arguments, the induction hypotheses,
and the generalized variables.

This work is done by `Lean.Elab.Tactic.deduplicate`.

<!--
Let `Γ` and `Δ` represent telescopes.
Generally, a set of mutual inductive types consists of a set of inductive types
that share a common telescope of parameters:

```lean
inductive I₁ Γ : Γ₁ → Sort
...
inductive Iₙ Γ : Γₙ → Sort
```

along with a set of constructors for these inductive types:

```lean
  | c₁ : Δ₁ → Ξ₁ → Iᵢ₁
  ...
  | cₘ : Δₘ → Ξₘ → Iᵢₘ
```

where `Ξᵢ` is a nondependent telescope of the form:

```lean
  (Δᵢ₁ → Iᵢⱼ₁) → ... → (Δᵢₖ → Iᵢⱼₖ)
```

with `i₁, ..., iₘ, ij₁, ..., ijₖ ∈ [1..n]`,
and none of `I₁, ..., Iₙ, c₁, ..., cₘ` are free in any `Γ`, `Δ`.
For each inductive, a recursor is generated,
all of which take the same parameters `ps : Γ`, `n` motives, and `m` cases.
The motives are of the form:

```lean
P₁ : ∀ (xs₁ : Γ₁), I₁ ps xs₁ → Sort
...
Pₙ : ∀ (xsₙ : Γₙ), Iₙ ps xsₙ → Sort
```

and the cases are of the form:

```lean
g₁ : ∀ (ys₁ : Δ₁) (hs₁ : Ξ₁),
     (∀ (zs₁₁ : Δ₁₁), P₁ⱼ₁ _ (hs₁₁ zs₁₁)) →
     ...
     (∀ (zs₁ₖ : Δ₁ₖ), P₁ⱼₖ _ (hs₁ₖ zs₁ₖ)) →
     Pᵢ₁ _ (c₁ ys₁ hs₁)
...
gₘ : ∀ (ysₘ : Δₘ) (hsₘ : Ξₘ),
     (∀ (zsₘ₁ : Δₘ₁), Pₘⱼ₁ _ (hsₘ₁ zsₘ₁)) →
     ...
     (∀ (zsₘₖ : Δₘₖ), Pₘⱼₖ _ (hsₘₖ zsₘₖ)) →
     Pᵢₘ _ (cₘ ysₘ hsₘ)
```

The recursor `Iᵢ.rec` then ends in `∀ (xsᵢ : Γᵢ) (h : Iᵢ ps xsᵢ), Pᵢ xsᵢ h`.
-->
