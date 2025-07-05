import MkAll
import MutualInduction

@[mk_all α β]
inductive Fan (α β : Type) : Type where
  | nil : Fan α β
  | cons : (Nat → α) → (Nat → β) → (Nat → Fan α β) → Fan α β
open Fan

inductive Tree (α : Type) : Type where
  | node : α → Fan (Tree α) (Tree α) → Tree α
open Tree

@[simp]
noncomputable def Tree.elim {α} {P : Tree α → Type}
  (node : ∀ {x t}, Fan.all P P t → P (node x t)) : ∀ t, P t := by
  intro t
  induction t using Tree.rec (motive_2 := Fan.all P P)
  all_goals first | (repeat' constructor) <;> assumption | apply_rules
  -- Tree.rec (motive_2 := Fan.all P)
  --   (λ _ _ ↦ hnode) ⟨⟩ (λ _ _ ihα iht ↦ ⟨ihα, iht⟩)

theorem Tree.ielim {α} {P : Tree α → Prop}
  (node : ∀ {x t}, Fan.iall P P t → P (node x t)) : ∀ t, P t := by
  intro t
  induction t using Tree.rec (motive_2 := Fan.iall P P)
  all_goals first | (repeat' constructor) <;> assumption | apply_rules

@[mk_all α]
inductive IFan (α : Prop) : Prop where
  | nil : IFan α
  | cons : (Nat → α) → (Nat → IFan α) → IFan α
open IFan

inductive ITree (α : Type) : Prop where
  | node : α → IFan (ITree α) → ITree α
open ITree

@[induction_eliminator]
theorem ITree.elim {α} {P : ITree α → Prop}
  (node : ∀ {x t}, IFan.all P t → P (node x t)) : ∀ t, P t := by
  intro t
  induction t using ITree.rec (motive_2 := IFan.all P)
  all_goals first | (repeat' constructor) <;> assumption | apply_rules

@[mk_all α]
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : ∀ n, α → Vec α n → Vec α (n + 1)

inductive VTree (α : Type) : Type where
  | node : ∀ n, α → Vec (VTree α) n → VTree α

theorem VTree.ielim {α} {P : VTree α → Prop}
  (node : ∀ {n x t}, Vec.iall P t → P (node n x t)) : ∀ t, P t := by
  intro t
  induction t using VTree.rec (motive_2 := λ _ ↦ Vec.iall P)
  all_goals first | (repeat' constructor) <;> assumption | apply_rules

@[induction_eliminator]
noncomputable def VTree.elim {α} {P : VTree α → Type}
  (node : ∀ {n x t}, Vec.all P t → P (node n x t)) : ∀ t, P t := by
  intro t
  induction t using VTree.rec (motive_2 := λ _ ↦ Vec.all P)
  all_goals first | (repeat' constructor) <;> assumption | apply_rules

noncomputable def VTree.sum (vt : VTree Nat) : Nat := by
  induction vt
  case node k vec all =>
  induction vec
  case nil => exact k
  case cons vt ih =>
    simp [Vec.all] at all
    let ⟨n, m⟩ := all
    exact n + (ih m)
