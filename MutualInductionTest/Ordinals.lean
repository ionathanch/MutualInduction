import MutualInduction

mutual
inductive Ordinal : Type where
  | succ : Ordinal → Ordinal
  | limit : Ordinals → Ordinal

inductive Ordinals : Type where
  | nil : Ordinals
  | cons : Ordinal → Ordinals → Ordinals
end
open Ordinal Ordinals

mutual
inductive Le : Ordinal → Ordinal → Prop where
  | succ {i j} : Le i j → Le (.succ i) (.succ j)
  | under {i js} : LeUnder i js → Le i (.limit js)
  | over {is j} : LeOver is j → Le (.limit is) j

inductive LeUnder : Ordinal → Ordinals → Prop where
  | underHere {i j js} : Le i j → LeUnder i (.cons j js)
  | underThere {i j js} : LeUnder i js → LeUnder i (.cons j js)

inductive LeOver : Ordinals → Ordinal → Prop where
  | overNil {j} : LeOver .nil j
  | overCons {i is j} : Le i j → LeOver is j → LeOver (.cons i is) j
end
open LeUnder LeOver

def zero := Ordinal.limit .nil
theorem zeroLe {i} : Le zero i := Le.over .overNil
theorem noLeZero {i} : Le (.succ i) zero → False := by
  intro le; cases le
  case under leUnder => cases leUnder

theorem leInd
  -- motives
  (P : ∀ {i j}, Le i j → Prop)
  (Q : ∀ {i js}, LeUnder i js → Prop)
  (R : ∀ {is j}, LeOver is j → Prop)
  -- Le subgoals
  (succ : ∀ {i j}
    (h : Le i j),
    P h → P (.succ h))
  (under : ∀ {i js}
    (h : LeUnder i js),
    Q h → P (.under h))
  (over : ∀ {is j}
    (h : LeOver is j),
    R h → P (.over h))
  -- LeUnder subgoals
  (underHere : ∀ {i j js}
    (h : Le i j),
    P h → Q (.underHere (js := js) h))
  (underThere : ∀ {i j js}
    (h : LeUnder i js),
    Q h → Q (.underThere (j := j) h))
  -- LeOver subgoals
  (overNil : ∀ {j}, R (.overNil (j := j)))
  (overCons : ∀ {i is j}
    (hle : Le i j)
    (h : LeOver is j),
    P hle → R h → R (.overCons hle h))
  : (∀ {i j} (h : Le i j), P h) ∧
    (∀ {i js} (h : LeUnder i js), Q h) ∧
    (∀ {is j} (h : LeOver is j), R h) := by
  repeat' constructor
  case' left => intro _ _ le
  case' right.left => intro _ _ leunder
  case' right.right => intro _ _ leover
  mutual_induction | left => le | right.left => leunder | right.right => leover
  case underThere ih => apply underThere _ ih
  all_goals apply_rules

@[simp]
def succOrdinals : Ordinals → Ordinals
  | nil => nil
  | cons i is => cons (succ i) (succOrdinals is)

theorem leSuccInv' :
  (∀ {i j}, Le (succ i) (succ j) → Le i j) ∧
  (∀ {i js}, LeUnder (succ i) (succOrdinals js) → LeUnder i js) ∧
  (∀ {is j}, LeOver (succOrdinals is) (succ j) → LeOver is j) := by
  repeat' constructor
  case' left =>
    intro i j h
    generalize ei : succ i = si at h
    generalize ej : succ j = sj at h
  case' right.left =>
    intro i js h
    generalize ei : succ i = si at h
    generalize ejs : succOrdinals js = sjs at h
  case' right.right =>
    intro is j h
    generalize eis : succOrdinals is = sis at h
    generalize ej : succ j = sj at h
  mutual_induction | left => h | right.left => h | right.right => h
  case succ ih =>
    injection ei with ei; subst ei
    injection ej with ej; subst ej
    assumption
  case under => injection ej
  case over => injection ei
  case underHere =>
    subst ei; cases js
    case nil => unfold succOrdinals at ejs; injection ejs
    case cons ih _ _ =>
      injection ejs with e₁ e₂; subst e₁; subst e₂
      exact underHere (ih rfl rfl)
  case underThere =>
    subst ei; cases js
    case nil => unfold succOrdinals at ejs; injection ejs
    case cons ih _ _ =>
      injection ejs with e₁ e₂; subst e₁; subst e₂
      exact underThere (ih rfl rfl)
  case overNil =>
    cases is
    case nil => constructor
    case cons => injection eis
  case overCons =>
    subst ej; cases is
    case nil => constructor
    case cons ihle ihleover _ _ =>
      injection eis with e₁ e₂; subst e₁; subst e₂
      exact overCons (ihle rfl rfl) (ihleover rfl rfl)

theorem leSuccInv : ∀ {i j}, Le (.succ i) (.succ j) → Le i j := by
  intro i j le
  let ⟨h, _, _⟩ := leSuccInv'
  exact h le

theorem leUnderSuccInv : ∀ {i js}, LeUnder (.succ i) (succOrdinals js) → LeUnder i js := by
  intro i js leUnder
  let ⟨_, h, _⟩ := leSuccInv'
  exact h leUnder

theorem leOverSuccInv : ∀ {is j}, LeOver (succOrdinals is) (.succ j) → LeOver is j := by
  intro is j leOver
  let ⟨_, _, h⟩ := leSuccInv'
  exact h leOver

theorem leSucc :
  (∀ {i j}, Le i j → Le i (.succ j)) ∧
  (∀ {i js}, LeUnder i js → LeUnder i (succOrdinals js)) ∧
  (∀ {is j}, LeOver is j → LeOver is (.succ j)) := by
  repeat' constructor
  all_goals intros _ _ h
  mutual_induction | left => h | right.left => h | right.right => h
  all_goals try simp
  case succ ih => exact .succ ih
  case under i _ _ _ =>
    cases i
    case succ ih => constructor; constructor; apply leUnderSuccInv ih
    case limit => constructor; sorry
  case over => constructor; assumption
  case underHere => apply LeUnder.underHere; assumption
  case underThere => apply LeUnder.underThere; assumption
  case overNil => constructor
  case overCons => constructor; assumption; assumption
