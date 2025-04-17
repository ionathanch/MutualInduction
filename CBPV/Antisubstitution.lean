import CBPV.NormalInd

open ValType ComType Val Com

/-*-----------------
  Antisubstitution
-----------------*-/

theorem antisubstitution {σ} :
  (∀ {m}, SNeCom (substCom σ m) → SNeCom m) ∧
  (∀ {v}, SNVal  (substVal σ v) → SNVal v)  ∧
  (∀ {m}, SNCom  (substCom σ m) → SNCom m)  ∧
  (∀ {m n}, substCom σ m ⤳ n → (∃ n', n = substCom σ n' ∧ m ⤳ n') ∨ SNeCom m) := by
  refine ⟨λ snem ↦ ?snecom, λ snv ↦ ?snval, λ snm ↦ ?sncom, λ r ↦ ?srcom⟩
  case' srcom  => generalize e : substCom σ _ = m' at r
  case' sncom  => generalize e : substCom σ _ = m' at snm
  case' snval  => generalize e : substVal σ _ = v' at snv
  case' snecom => generalize e : substCom σ _ = m' at snem
  mutual_induction snem, snv, snm, r generalizing σ
  case snecom.force ih m =>
    cases m <;> try contradiction
    injection e with e
    case force v =>
    let ⟨_, e⟩ := ih; subst e
    cases v <;> try contradiction
    exact .force .var
  case snecom.app ihm ihv m =>
    cases m <;> try contradiction
    injection e with em ev
    exact .app (ihm em) (ihv ev)
  case snecom.letin ihm ihn m =>
    cases m <;> try contradiction
    injection e with em en
    exact .letin (ihm em) (ihn en)
  case snecom.case snev _ ihv ihm ihn m =>
    cases m <;> try contradiction
    injection e with ev em en
    case case v _ _ =>
    let ⟨_, e⟩ := snev; subst e
    cases v <;> try contradiction
    exact .case .var (ihm em) (ihn en)
  case snval.var v =>
    cases v <;> try contradiction
    exact .var
  case snval.unit v =>
    cases v <;> try injection e
    all_goals repeat constructor
  case snval.inl ih v =>
    cases v <;> try contradiction
    case var => exact .var
    case inl =>
    injection e with e
    exact .inl (ih e)
  case snval.inr ih v =>
    cases v <;> try contradiction
    case var => exact .var
    case inr =>
    injection e with e
    exact .inr (ih e)
  case snval.thunk ih v =>
    cases v <;> try contradiction
    case var => exact .var
    case thunk =>
    injection e with e
    exact .thunk (ih e)
  case sncom.lam ih m =>
    cases m <;> try contradiction
    injection e with e
    exact .lam (ih e)
  case sncom.ret ih m =>
    cases m <;> try contradiction
    injection e with e
    exact .ret (ih e)
  case sncom.ne ih _ => exact .ne (ih e)
  case sncom.red ihr ihm _ =>
    match ihr e with
    | .inl ⟨_, e, r⟩ =>
      exact .red r (ihm (Eq.symm e))
    | .inr snem => exact .ne snem
  case srcom.thunk ih m =>
    cases m <;> try contradiction
    injection e with e
    case force v =>
    cases v <;> try contradiction
    case var => exact .inr (.force .var)
    case thunk =>
    injection e with e
    exact .inl ⟨_, Eq.symm e, .thunk⟩
  case srcom.lam ih m =>
    cases m <;> try contradiction
    injection e with em ev
    case app m _ =>
    cases m <;> try contradiction
    injection em with em
    subst ev em; rw [substDist]
    exact .inl ⟨_, rfl, .lam (ih rfl)⟩
  case srcom.ret ih m =>
    cases m <;> try contradiction
    injection e with ev em
    case letin m _ =>
    cases m <;> try contradiction
    injection ev with ev
    subst ev em; rw [substDist]
    exact .inl ⟨_, rfl, .ret (ih rfl)⟩
  case srcom.inl ihv ihn m =>
    cases m <;> try contradiction
    injection e with ev em en
    case case v _ _ =>
    cases v <;> try contradiction
    case var m n _ => exact .inr (.case .var sorry (ihn en))
    case inl =>
    injection ev with ev
    subst ev em en; rw [substDist]
    exact .inl ⟨_, rfl, .inl (ihv rfl) (ihn rfl)⟩
  case srcom.inr ihv ihm m =>
    cases m <;> try contradiction
    injection e with ev em en
    case case v _ _ =>
    cases v <;> try contradiction
    case var m n _ => exact .inr (.case .var (ihm em) sorry)
    case inr =>
    injection ev with ev
    subst ev em en; rw [substDist]
    exact .inl ⟨_, rfl, .inr (ihv rfl) (ihm rfl)⟩
  case srcom.app ihv ihm m =>
    cases m <;> try contradiction
    injection e with em ev
    match ihm em with
    | .inl ⟨_, em, r⟩ =>
      subst em ev
      exact .inl ⟨.app _ _, rfl, .app (ihv rfl) r⟩
    | .inr snem => exact .inr (.app snem (ihv ev))
  case srcom.letin ihn ihm m =>
    cases m <;> try contradiction
    injection e with em en
    match ihm em with
    | .inl ⟨_, em, r⟩ =>
      subst em en
      exact .inl ⟨.letin _ _, rfl, .letin (ihn rfl) r⟩
    | .inr snem => exact .inr (.letin snem (ihn en))

theorem SNCom.antisubstitution {m} {v : Val} (h : SNCom (m⦃v⦄)) : SNCom m :=
  _root_.antisubstitution.right.right.left h

/-*-----------------------------------------------
  Inversion lemmas depending on antisubstitution
-----------------------------------------------*-/

theorem SNCom.app_inv {m v} (h : SNCom (app m v)) : SNCom m ∧ SNVal v := by
  generalize e : app m v = n at h
  mutual_induction h generalizing m v
  all_goals first | contradiction | subst e
  case ne sne => match sne with
  | .app snem snv => exact ⟨.ne snem, snv⟩
  case red sn ih r =>
    cases r
    case lam snv => exact ⟨.lam sn.antisubstitution, snv⟩
    case app r _ => let ⟨snn, snv⟩ := ih rfl; exact ⟨.red r snn, snv⟩

theorem SNCom.letin_inv {m n} (h : SNCom (letin m n)) : SNCom m ∧ SNCom n := by
  generalize e : letin m n = mn at h
  mutual_induction h generalizing m n
  all_goals first | contradiction | subst e
  case ne sne => match sne with
  | .letin snem snn => exact ⟨.ne snem, snn⟩
  case red sn ih r =>
    cases r
    case ret snv => exact ⟨.ret snv, sn.antisubstitution⟩
    case letin r _ => let ⟨snm, snn⟩ := ih rfl; exact ⟨.red r snm, snn⟩
