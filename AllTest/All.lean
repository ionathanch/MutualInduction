import MkAll

@[mk_all α β]
inductive Fan (α β : Type) : Type where
  | nil : Fan α β
  | cons : (Nat → α) → (Nat → β) → (Nat → Fan α β) → Fan α β
open Fan

inductive Tree (α : Type) : Type where
  | node : α → Fan (Tree α) (Tree α) → Tree α
open Tree

noncomputable def Tree.elim {α} (P : Tree α → Type)
  (hnode : ∀ {x t}, Fan.all P P t → P (node x t)) : ∀ t, P t := by
  intro t
  induction t using Tree.rec (motive_2 := Fan.all P P)
  all_goals first | apply hnode | repeat' constructor
  all_goals assumption
  -- Tree.rec (motive_2 := Fan.all P)
  --   (λ _ _ ↦ hnode) ⟨⟩ (λ _ _ ihα iht ↦ ⟨ihα, iht⟩)

@[mk_all α]
inductive IFan (α : Prop) : Prop where
  | nil : IFan α
  | cons : (Nat → α) → (Nat → IFan α) → IFan α
open IFan

inductive ITree (α : Type) : Prop where
  | node : α → IFan (ITree α) → ITree α
open ITree

theorem ITree.elim {α} (P : ITree α → Prop)
  (hnode : ∀ {x t}, IFan.all P t → P (node x t)) : ∀ t, P t := by
  intro t
  induction t using ITree.rec (motive_2 := IFan.all P)
  case node x _ ih => exact hnode (x := x) ih
  case nil => constructor
  case cons => constructor <;> assumption

@[mk_all α]
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : ∀ n, α → Vec α n → Vec α (n + 1)

inductive VTree (α : Type) : Type where
  | node : ∀ n, α → Vec (VTree α) n → VTree α

theorem VTree.elim {α} (P : VTree α → Prop)
  (hnode : ∀ {n x t}, Vec.iall P t → P (node n x t)) : ∀ t, P t := by
  intro t
  induction t using VTree.rec (motive_2 := λ _ ↦ Vec.iall P)
  case node ih => exact hnode ih
  case nil => constructor
  case cons => constructor <;> assumption
