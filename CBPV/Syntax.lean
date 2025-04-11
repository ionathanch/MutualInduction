import MutualInduction

open Nat

@[simp]
def cons {A : Type} (x : A) (ξ : Nat → A) : Nat → A
  | 0 => x
  | n + 1 => ξ n
infixr:50 "+:" => cons

/-*------
  Types
------*-/

mutual
inductive ValType : Type where
  | Unit : ValType
  | U : ComType → ValType

inductive ComType : Type where
  | F : ValType → ComType
  | Arr : ValType → ComType → ComType
end
open ValType ComType

/-*------
  Terms
------*-/

mutual
inductive Val : Type where
  | var : Nat → Val
  | unit : Val
  | thunk : Com → Val

inductive Com : Type where
  | force : Val → Com
  | lam : Com → Com
  | app : Com → Val → Com
  | ret : Val → Com
  | letin : Com → Com → Com
end
open Val Com

theorem appCong {m m' v v'} : m = m' → v = v' → app m v = app m' v'
  | rfl, rfl => rfl

theorem letinCong {m m' n n'} : m = m' → n = n' → letin m n = letin m' n'
  | rfl, rfl => rfl

/-*------------------
  Lifting renamings
------------------*-/

@[simp]
def lift (ξ : Nat → Nat) : Nat → Nat :=
  zero +: (succ ∘ ξ)

-- Lifting respects renaming extensionality
theorem liftExt ξ ζ (h : ∀ x, ξ x = ζ x) : ∀ x, lift ξ x = lift ζ x := by
  intro x; cases x <;> simp [h]

-- Lifting identity renaming does nothing
theorem liftId ξ (h : ∀ x, ξ x = x) : ∀ x, lift ξ x = x := by
  intro x; cases x <;> simp [h]

-- Lifting composes
theorem liftComp ξ ζ ς (h : ∀ x, (ξ ∘ ζ) x = ς x) :
  ∀ x, (lift ξ ∘ lift ζ) x = lift ς x := by
  intro x; cases x <;> simp
  case succ => apply h

-- Lifting commutes with succ
theorem liftSucc ξ : ∀ x, (lift ξ ∘ succ) x = (succ ∘ ξ) x := by
  intro x; cases x <;> simp

/-*-------------------
  Applying renamings
-------------------*-/

mutual
@[simp]
def renameVal (ξ : Nat → Nat) : Val → Val
  | var s => var (ξ s)
  | unit => unit
  | thunk m => thunk (renameCom ξ m)

@[simp]
def renameCom (ξ : Nat → Nat) : Com → Com
  | force v => force (renameVal ξ v)
  | lam m => lam (renameCom (lift ξ) m)
  | app m v => app (renameCom ξ m) (renameVal ξ v)
  | ret v => ret (renameVal ξ v)
  | letin m n => letin (renameCom ξ m) (renameCom (lift ξ) n)
end

-- Renaming extensionality
theorem renameExt ξ ζ (h : ∀ x, ξ x = ζ x) :
  (∀ v, renameVal ξ v = renameVal ζ v) ∧
  (∀ m, renameCom ξ m = renameCom ζ m) := by
  refine ⟨λ v ↦ ?val, λ m ↦ ?com⟩
  mutual_induction v, m generalizing ξ ζ
  all_goals simp; try constructor
  all_goals apply_rules [liftExt]

def renameValExt ξ ζ h := (renameExt ξ ζ h).left
def renameCompExt ξ ζ h := (renameExt ξ ζ h).right

-- Applying identity renaming does nothing
theorem renameId :
  (∀ v, renameVal id v = v) ∧
  (∀ m, renameCom id m = m) := by
  refine ⟨λ v ↦ ?val, λ m ↦ ?com⟩
  mutual_induction v, m
  all_goals simp; try constructor
  all_goals try assumption
  all_goals unfold Function.comp id
  all_goals rw [renameCompExt (0 +: succ) id]
  all_goals apply_rules [liftId]

def renameValId := renameId.left
def renameComId := renameId.right

-- Renamings compose
theorem renameComp' ξ ζ ς (h : ∀ x, (ξ ∘ ζ) x = ς x) :
  (∀ v, (renameVal ξ ∘ renameVal ζ) v = renameVal ς v) ∧
  (∀ m, (renameCom ξ ∘ renameCom ζ) m = renameCom ς m) := by
  refine ⟨λ v ↦ ?val, λ m ↦ ?comp⟩
  mutual_induction v, m generalizing ξ ζ ς
  all_goals simp; try constructor
  all_goals apply_rules [liftComp]

def renameValComp ξ ζ v : renameVal ξ (renameVal ζ v) = renameVal (ξ ∘ ζ) v :=
  (renameComp' ξ ζ (ξ ∘ ζ) (λ _ ↦ rfl)).left v

def renameComComp ξ ζ v : renameCom ξ (renameCom ζ v) = renameCom (ξ ∘ ζ) v :=
  (renameComp' ξ ζ (ξ ∘ ζ) (λ _ ↦ rfl)).right v

/-*----------------------
  Lifting substitutions
----------------------*-/

@[simp]
def up (σ : Nat → Val) : Nat → Val :=
  var 0 +: (renameVal succ ∘ σ)
prefix:95 "⇑" => up

-- Lifting twice pushes renamings inwards
theorem upUp σ x : (⇑ ⇑ σ) x = (var 0 +: var 1 +: (renameVal succ ∘ renameVal succ ∘ σ)) x := by
  cases x; rfl
  case succ n => cases n <;> rfl

-- Lifting var "substitution" does nothing
theorem upId σ (h : ∀ x, σ x = var x) : ∀ x, (⇑ σ) x = var x := by
  intro n; cases n <;> simp [h]

-- Lifting respects subsitution extensionality
theorem upExt σ τ (h : ∀ x, σ x = τ x) : ∀ x, (⇑ σ) x = (⇑ τ) x := by
  intro n; cases n <;> simp [h]

-- Lifting commutes with composition
theorem upLift ξ σ τ (h : ∀ x, (σ ∘ ξ) x = τ x) : ∀ x, (⇑ σ ∘ lift ξ) x = (⇑ τ) x := by
  intro n; cases n <;> simp [← h]

-- Lifting commutes with succ
theorem upSucc σ : ∀ x, (⇑ σ ∘ succ) x = (renameVal succ ∘ σ) x := by
  intro n; cases n <;> simp

-- Lifting commutes with injection of renamings into substitutions
theorem upVar ξ : ∀ x, (var ∘ lift ξ) x = (⇑ (var ∘ ξ)) x := by
  intro n; cases n <;> simp

-- Lifting commutes with renaming
theorem upRename ξ σ τ (h : ∀ x, (renameVal ξ ∘ σ) x = τ x) : ∀ x, (renameVal (lift ξ) ∘ ⇑ σ) x = (⇑ τ) x := by
  intro n; cases n; simp
  case succ n => calc
    (renameVal (lift ξ) ∘ renameVal succ) (σ n)
      = renameVal (lift ξ ∘ succ) (σ n)      := by simp [renameValComp]
    _ = (renameVal (succ ∘ ξ)) (σ n)         := by rfl
    _ = (renameVal succ ∘ renameVal ξ) (σ n) := by simp [renameValComp]
    _ = (renameVal succ (renameVal ξ (σ n))) := by rfl
    _ = renameVal succ (τ n)                 := by rw [← h]; rfl

/-*-----------------------
  Applying substitutions
-----------------------*-/

mutual
@[simp]
def substVal (σ : Nat → Val) : Val → Val
  | var s => σ s
  | unit => unit
  | thunk m => thunk (substCom σ m)

@[simp]
def substCom (σ : Nat → Val) : Com → Com
  | force v => force (substVal σ v)
  | lam m => lam (substCom (⇑ σ) m)
  | app m v => app (substCom σ m) (substVal σ v)
  | ret v => ret (substVal σ v)
  | letin m n => letin (substCom σ m) (substCom (⇑ σ) n)
end
notation:50 v "⦃" σ "⦄" => substVal σ v
notation:50 m "⦃" σ "⦄" => substCom σ m
notation:50 m "⦃" v "⦄" => substCom (v +: var) m

-- Substitution extensionality
theorem substExt σ τ (h : ∀ x, σ x = τ x) :
  (∀ v, substVal σ v = substVal τ v) ∧
  (∀ m, substCom σ m = substCom τ m) := by
  refine ⟨λ v ↦ ?val, λ m ↦ ?com⟩
  mutual_induction v, m generalizing σ τ
  all_goals simp; try constructor
  all_goals apply_rules [upExt]

def substValExt σ τ h := (substExt σ τ h).left
def substComExt σ τ h := (substExt σ τ h).right

-- Applying var "substitution" does nothing
theorem substId σ (h : ∀ x, σ x = var x) :
  (∀ v, substVal σ v = v) ∧
  (∀ m, substCom σ m = m) := by
  refine ⟨λ v ↦ ?val, λ m ↦ ?com⟩
  mutual_induction v, m generalizing σ
  all_goals simp; try constructor
  all_goals apply_rules [upId]

def substValId := (substId var (λ _ ↦ rfl)).left
def substComId := (substId var (λ _ ↦ rfl)).right

-- Substitution/renaming compositionality
theorem substRename ξ σ τ (h : ∀ x, (σ ∘ ξ) x = τ x) :
  (∀ v, substVal σ (renameVal ξ v) = substVal τ v) ∧
  (∀ m, substCom σ (renameCom ξ m) = substCom τ m) := by
  refine ⟨λ v ↦ ?val, λ m ↦ ?com⟩
  mutual_induction v, m generalizing ξ σ τ
  all_goals simp; try constructor
  all_goals apply_rules [upLift]

def substRenameVal ξ σ := (substRename ξ σ (σ ∘ ξ) (λ _ ↦ rfl)).left
def substRenameCom ξ σ := (substRename ξ σ (σ ∘ ξ) (λ _ ↦ rfl)).right

-- Renaming/substitution compositionality
theorem renameSubst ξ σ τ (h : ∀ x, (renameVal ξ ∘ σ) x = τ x) :
  (∀ v, renameVal ξ (substVal σ v) = substVal τ v) ∧
  (∀ m, renameCom ξ (substCom σ m) = substCom τ m) := by
  refine ⟨λ v ↦ ?val, λ m ↦ ?com⟩
  mutual_induction v, m generalizing ξ σ τ
  all_goals simp; try constructor
  all_goals apply_rules [upRename]

def renameSubstVal ξ σ := (renameSubst ξ σ (renameVal ξ ∘ σ) (λ _ ↦ rfl)).left
def renameSubstCom ξ σ := (renameSubst ξ σ (renameVal ξ ∘ σ) (λ _ ↦ rfl)).right

-- Lifting commutes with substitution
theorem upSubst ρ σ τ (h : ∀ x, (substVal ρ ∘ σ) x = τ x) :
  (∀ x, (substVal (⇑ ρ) ∘ (⇑ σ)) x = (⇑ τ) x) := by
  intro n; cases n; rfl
  case succ n => calc
    (substVal (⇑ ρ) ∘ renameVal succ) (σ n)
    _ = substVal (⇑ ρ ∘ succ) (σ n)         := by rw [← substRenameVal]; rfl
    _ = substVal (renameVal succ ∘ ρ) (σ n) := by rfl
    _ = (renameVal succ ∘ substVal ρ) (σ n) := by rw [← renameSubstVal]; rfl
    _ = renameVal succ (substVal ρ (σ n))   := by rfl
    _ = renameVal succ (τ n)                := by rw [← h]; rfl

-- Substitution compositionality
theorem substComp ρ σ τ (h : ∀ x, (substVal ρ ∘ σ) x = τ x) :
  (∀ v, (substVal ρ ∘ substVal σ) v = substVal τ v) ∧
  (∀ m, (substCom ρ ∘ substCom σ) m = substCom τ m) := by
  refine ⟨λ v ↦ ?val, λ m ↦ ?com⟩
  mutual_induction v, m generalizing ρ σ τ
  all_goals simp; try constructor
  all_goals apply_rules [upSubst]

def substValComp ρ σ := (substComp ρ σ (substVal ρ ∘ σ) (λ _ ↦ rfl)).left
def substComComp ρ σ := (substComp ρ σ (substVal ρ ∘ σ) (λ _ ↦ rfl)).right

theorem renameToSubst ξ :
  (∀ v, renameVal ξ v = substVal (var ∘ ξ) v) ∧
  (∀ m, renameCom ξ m = substCom (var ∘ ξ) m) := by
  refine ⟨λ v ↦ ?val, λ m ↦ ?com⟩
  mutual_induction v, m generalizing ξ
  all_goals simp [-up] <;> try constructor
  all_goals try rw [← substComExt _ _ (upVar ξ)]
  all_goals apply_rules

def renameToSubstVal ξ := (renameToSubst ξ).left
def renameToSubstCom ξ := (renameToSubst ξ).right

/-*-------------------------------------------------
  Handy dandy derived renaming substitution lemmas
-------------------------------------------------*-/

theorem substValDrop v w : w = substVal (v +: var) (renameVal succ w) := by
  calc
    w = substVal var w                         := by rw [substValId]
    _ = substVal (v +: var) (renameVal succ w) := by rw [substRenameVal]; rfl

theorem substUnion σ a m : substCom (a +: σ) m = substCom (a +: var) (substCom (⇑ σ) m) := by
  calc
    substCom (a +: σ) m
    _ = substCom (substVal (a +: var) ∘ (var 0 +: (renameVal succ ∘ σ))) m :=
        by apply substComExt; intro n; cases n <;> simp; rw [← substValDrop]
    _ = substCom (a +: var) (substCom (⇑ σ) m) :=
        by rw [← substComComp]; rfl

theorem renameDist ξ a m : substCom (renameVal ξ a +: var) (renameCom (lift ξ) m) = renameCom ξ (substCom (a +: var) m) := by
  calc
    substCom (renameVal ξ a +: var) (renameCom (lift ξ) m)
    _ = substCom ((renameVal ξ a +: var) ∘ lift ξ) m := by rw [substRenameCom]
    _ = substCom (renameVal ξ ∘ (a +: var)) m        := by apply substComExt; intro n; cases n <;> rfl
    _ = renameCom ξ (substCom (a +: var) m)          := by rw [← renameSubstCom]

theorem substToRename x m : substCom (var x +: var) m = renameCom (x +: id) m := by
  calc
    substCom (var x +: var) m
    _ = substCom (var ∘ (x +: id)) m := by apply substComExt; intro n; cases n <;> simp
    _ = renameCom (x +: id) m        := by rw [renameToSubstCom]

theorem substComVar σ x m : substCom (var x +: σ) m = renameCom (x +: id) (substCom (⇑ σ) m) := by
  calc
    substCom (var x +: σ) m
    _ = substCom (var x +: var) (substCom (⇑ σ) m) := substUnion σ (var x) m
    _ = renameCom (x +: id) (substCom (⇑ σ) m)     := substToRename x _

/-
theorem renameLiftRename ξ a : rename succ (rename ξ a) = rename (lift ξ) (rename succ a) := by
  calc
    rename succ (rename ξ a)
      = rename (succ ∘ ξ) a             := by rw [renameComp]
    _ = rename (lift ξ ∘ succ) a        := by rw [renameExt]; exact liftSucc ξ
    _ = rename (lift ξ) (rename succ a) := by rw [← renameComp]

theorem renameUpSubst σ a : rename succ (subst σ a) = subst (⇑ σ) (rename succ a) := by
  calc
    rename succ (subst σ a)
      = subst (rename succ ∘ σ) a   := by rw [renameSubst]
    _ = subst (⇑ σ ∘ succ) a        := by rw [substExt]; exact upSucc σ
    _ = subst (⇑ σ) (rename succ a) := by rw [substRename]

theorem renameDist ξ a s : subst (rename ξ a +: var) (rename (lift ξ) s) = rename ξ (subst (a +: var) s) := by
  calc
    subst (rename ξ a +: var) (rename (lift ξ) s)
    _ = subst ((rename ξ a +: var) ∘ lift ξ) s := by rw [substRename]
    _ = subst (rename ξ ∘ (a +: var)) s        := by apply substExt; intro n; cases n <;> rfl
    _ = rename ξ (subst (a +: var) s)          := by rw [← renameSubst]

theorem substDist σ a s : subst (subst σ a +: var) (subst (⇑ σ) s) = subst σ (subst (a +: var) s) := by
  calc
    subst (subst σ a +: var) (subst (⇑ σ) s)
      = subst (subst σ a +: σ) s       := by rw [← substUnion]
    _ = subst (subst σ ∘ (a +: var)) s := by apply substExt; intro n; cases n <;> rfl
    _ = (subst σ ∘ subst (a +: var)) s := by rw [← substComp]

theorem substToRename x s : subst (var x +: var) s = rename (x +: id) s := by
  calc
    subst (var x +: var) s
      = subst (var ∘ (x +: id)) s := by apply substExt; intro n; cases n <;> simp
    _ = rename (x +: id) s        := by rw [renameToSubst]
-/

/-*------------------------
  Contexts and membership
------------------------*-/

inductive Ctxt : Type where
  | nil : Ctxt
  | cons : Ctxt → ValType → Ctxt
notation:50 "⬝" => Ctxt.nil
infixl:50 "∷" => Ctxt.cons

inductive In : Nat → ValType → Ctxt → Prop where
  | here {Γ A} : In 0 A (Γ ∷ A)
  | there {Γ x A B} : In x A Γ → In (succ x) A (Γ ∷ B)
notation:40 Γ:41 "∋" x:41 "∶" A:41 => In x A Γ
