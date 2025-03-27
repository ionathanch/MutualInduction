import MutualInduction

mutual
inductive Tree : Prop where
  | node : Forest → Tree
inductive Forest : Prop where
  | nil : Forest
  | cons : Tree → Forest → Forest
end
open Tree Forest

mutual
inductive AllTree (P : Tree → Prop) (Q : Forest → Prop) : Tree → Prop where
  | node : ∀ {f}, Q f → AllForest P Q f → AllTree P Q (node f)
inductive AllForest (P : Tree → Prop) (Q : Forest → Prop) : Forest → Prop where
  | nil : AllForest P Q nil
  | cons : ∀ {t f}, P t → Q f → AllTree P Q t → AllForest P Q f → AllForest P Q (cons t f)
end

theorem elim (P : Tree → Prop) (Q : Forest → Prop)
  (ht : ∀ {t}, AllTree P Q t → P t)
  (hf : ∀ {f}, AllForest P Q f → Q f) :
  (∀ t, P t) ∧ (∀ f, Q f) := by
  constructor
  case' left  => intro t; apply ht
  case' right => intro f; apply hf
  mutual_induction f, t
  case node f ihf => exact AllTree.node (hf ihf) ihf
  case nil => exact AllForest.nil
  case cons t f iht ihf => exact AllForest.cons (ht iht) (hf ihf) iht ihf

inductive RoseTree (α : Type) : Type where
  | node : α → List (RoseTree α) → RoseTree α
open RoseTree

inductive List.All {α} (P : α → Prop) : List α → Prop where
  | nil : All P []
  | cons : ∀ {x xs}, P x → All P xs → All P (x :: xs)

theorem RoseTree.elim {α} (P : RoseTree α → Prop)
  (hnode : ∀ {x t}, List.All P t → P (node x t)) : ∀ t, P t := by
  intro t
  induction t using RoseTree.rec (motive_2 := List.All P)
  case node ih => exact hnode ih
  case nil => constructor
  case cons => constructor <;> assumption

inductive RoseTree.belowAll {α} {motive : RoseTree α → Prop} : RoseTree α → Prop where
  | node : ∀ {x t}, List.All motive t → List.All belowAll t → belowAll (node x t)

theorem RoseTree.brecOnAll {α} {P : RoseTree α → Prop}
  (hnode : ∀ {t}, RoseTree.belowAll (motive := P) t → P t) :
  ∀ t, P t := by
  intro t
  apply hnode
  induction t using RoseTree.elim
  case _ ts =>
    constructor
    induction ts <;> constructor
    apply hnode; assumption; assumption; assumption
