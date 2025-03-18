import «MutualInduction».MutualInduction

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

theorem all (P : Tree → Prop) (Q : Forest → Prop)
  (ht : ∀ {t}, AllTree P Q t → P t)
  (hf : ∀ {f}, AllForest P Q f → Q f) :
  (∀ t, P t) ∧ (∀ f, Q f) := by
  constructor
  case' left  => intro t; apply ht
  case' right => intro f; apply hf
  mutual_induction | left => t | right => f
  case node f ihf => exact AllTree.node (hf ihf) ihf
  case nil => exact AllForest.nil
  case cons t f iht ihf => exact AllForest.cons (ht iht) (hf ihf) iht ihf
