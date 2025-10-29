import MutualInduction
import Joint

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

joint
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
  theorem Le.ind {i j} (le : Le i j) : P le
  theorem LeUnder.ind {i js} (leunder : LeUnder i js) : Q leunder
  theorem LeOver.ind {is j} (leover : LeOver is j) : R leover
by
  mutual_induction le, leunder, leover
  case underThere ih => apply underThere _ ih
  all_goals apply_rules

@[simp]
def succOrdinals : Ordinals → Ordinals
  | nil => nil
  | cons i is => cons (succ i) (succOrdinals is)

joint
  theorem leSuccInv {i j} (h : Le (succ i) (succ j)) : Le i j
  theorem leUnderSuccInv {i js} (h : LeUnder (succ i) (succOrdinals js)) : LeUnder i js
  theorem leOverSuccInv {is j} (h : LeOver (succOrdinals is) (succ j)) : LeOver is j
by
  case' leSuccInv =>
    generalize ei : succ i = si at h
    generalize ej : succ j = sj at h
  case' leUnderSuccInv =>
    generalize ei : succ i = si at h
    generalize ejs : succOrdinals js = sjs at h
  case' leOverSuccInv =>
    generalize eis : succOrdinals is = sis at h
    generalize ej : succ j = sj at h
  mutual_induction h, h, h
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

joint
  theorem leSucc {i j} (h : Le i j) : Le i (.succ j)
  theorem leUnderSucc {i js} (h : LeUnder i js) : LeUnder i (succOrdinals js)
  theorem leOverSucc {is j} (h : LeOver is j) : LeOver is (.succ j)
by
  mutual_induction h, h, h
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
