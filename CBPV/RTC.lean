inductive RTC {A : Type} (R : A → A → Prop) : A → A → Prop
  | refl {a} : RTC R a a
  | trans {a b c} : R a b → RTC R b c → RTC R a c

@[refl] def RTC.rfl {m} := @RTC.refl m

def RTC.refl' {A R} (a : A) : RTC R a a := .refl

def RTC.trans' {A R} {a b c : A} (rab : RTC R a b) (rbc : RTC R b c) : RTC R a c := by
  induction rab
  case refl => exact rbc
  case trans => constructor <;> apply_rules

def RTC.once {A R} {a b : A} (r : R a b) : RTC R a b := .trans r .refl

instance {A} {R : A → A → Prop} : Trans R (RTC R) (RTC R) where
  trans := .trans

instance {A} {R : A → A → Prop} : Trans (RTC R) (RTC R) (RTC R) where
  trans := .trans'

instance {A} {R : A → A → Prop} : Trans R R (RTC R) where
  trans r₁ r₂ := .trans r₁ (.once r₂)

instance {A} {R : A → A → Prop} : Trans (RTC R) R (RTC R) where
  trans r₁ r₂ := .trans' r₁ (.once r₂)
