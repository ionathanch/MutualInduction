import CBPV.Equivalence

open Nat ValType ComType Val Com

theorem letLet {Γ n m m' A} {B : ComType}
  (hlet : Γ ⊢ letin n m ∶ F A)
  (hm' : Γ ∷ A ⊢ m' ∶ B) :
  Γ ⊨ letin (letin n m) m' ~ letin n (letin m (renameCom (lift succ) m')) ∶ B := by
  intro σ τ hστ
  let ⟨v₁, v₂, rv₁, rv₂, hA⟩ := (soundCom hlet σ τ hστ).ret_inv
  have r₁' : letin ((letin n m)⦃σ⦄) (m'⦃⇑ σ⦄) ⇒⋆ m'⦃v₁ +: σ⦄ := by
    rw [substUnion]; exact .trans' rv₁.let (.once .ζ)
  cases hlet with | letin hn hm =>
  let ⟨w₁, w₂, rw₁, rw₂, _⟩ := (soundCom hn σ τ hστ).ret_inv
  have rlet : letin (n⦃τ⦄) (m⦃⇑ τ⦄) ⇒⋆ m⦃w₂ +: τ⦄ := calc
    _ ⇒⋆ letin (ret w₂) (m⦃⇑ τ⦄) := rw₂.let
    _ ⇒  m⦃w₂ +: τ⦄ := by rw [substUnion]; exact .ζ
  let ⟨_, rlet₁, rlet₂⟩ := confluence rv₂ rlet
  rw [← rlet₁.ret_inv] at rlet₂
  have r₂' : (letin n (letin m (renameCom (lift succ) m')))⦃τ⦄ ⇒⋆ m'⦃v₂ +: τ⦄ := calc
    _ ⇒⋆ letin (ret w₂) (letin (m⦃⇑ τ⦄) ((renameCom (lift succ) m')⦃⇑⇑ τ⦄))
      := by simp only [substCom]; exact rw₂.let
    _ ⇒ (letin (m⦃⇑ τ⦄) ((renameCom (lift succ) m')⦃⇑⇑ τ⦄))⦃w₂⦄ := .ζ
    _ = letin (m⦃w₂ +: τ⦄) (m'⦃⇑τ⦄)
      := by simp only [substCom]; rw [← substUnion, renameDropSubst]
    _ ⇒⋆ letin (ret v₂) (m'⦃⇑τ⦄) := rlet₂.let
    _ ⇒ m'⦃v₂ +: τ⦄ := by rw [substUnion]; exact .ζ
  exact ℰ.bwds r₁' r₂' (soundCom hm' (v₁ +: σ) (v₂ +: τ) (semCtxt.cons hA hστ))

theorem appLet {Γ n m v A B}
  (hlet : Γ ⊢ letin n m ∶ Arr A B)
  (hv : Γ ⊢ v ∶ A) :
  Γ ⊨ app (letin n m) v ~ letin n (app m (renameVal succ v)) ∶ B := by
  intro σ τ hστ
  let ⟨n₁, n₂, r₁, r₂, hB⟩ := (soundCom hlet σ τ hστ).lam_inv
  have r₁' : app ((letin n m)⦃σ⦄) (v⦃σ⦄) ⇒⋆ n₁⦃v⦃σ⦄⦄ := .trans' r₁.app (.once .β)
  simp only [substCom] at *
  cases hlet with | letin hn hm =>
  let ⟨w₁, w₂, _, rw₂, hA'⟩ := (soundCom hn σ τ hστ).ret_inv
  let ⟨_, m₂, _, rm₂, _⟩ := (soundCom hm (w₁ +: σ) (w₂ +: τ) (semCtxt.cons hA' hστ)).lam_inv
  have rlet : letin (n⦃τ⦄) (m⦃⇑ τ⦄) ⇒⋆ lam m₂ := calc
    _ ⇒⋆ letin (ret w₂) (m⦃⇑ τ⦄) := rw₂.let
    _ ⇒  m⦃w₂ +: τ⦄ := by rw [substUnion]; exact .ζ
    _ ⇒⋆ lam m₂ := rm₂
  let ⟨_, rlam₁, rlam₂⟩ := confluence r₂ rlet
  rw [← rlam₂.lam_inv] at rlam₁; injection rlam₁.lam_inv with e; subst e
  clear rlet rlam₁ rlam₂
  have r₂' : letin (n⦃τ⦄) (app (m⦃⇑ τ⦄) (renameVal succ v⦃⇑ τ⦄))
      ⇒⋆ n₂⦃v⦃τ⦄⦄ := calc
    _ ⇒⋆ letin (ret w₂) (app (m⦃⇑ τ⦄) (renameVal succ v⦃⇑ τ⦄)) := rw₂.let
    _ ⇒  (app (m⦃⇑ τ⦄) (renameVal succ v⦃⇑ τ⦄))⦃w₂⦄ := .ζ
    _ = app (m⦃w₂ +: τ⦄) (v⦃τ⦄)
      := by simp only [substCom]; rw [← substUnion, ← renameUpSubstVal, ← substDropVal]
    _ ⇒⋆ app (lam n₂) (v⦃τ⦄) := rm₂.app
    _ ⇒  n₂⦃v⦃τ⦄⦄ := .β
  exact ℰ.bwds r₁' r₂' (hB _ _ (soundVal hv σ τ hστ))

theorem fstLet {Γ n m B₁ B₂}
  (hlet : Γ ⊢ letin n m ∶ Prod B₁ B₂) :
  Γ ⊨ fst (letin n m) ~ letin n (fst m) ∶ B₁ := by
  intro σ τ hστ
  let ⟨n₁, _, n₂, _, r₁, r₂, hB₁⟩ := (soundCom hlet σ τ hστ).fst
  have r₁' : fst ((letin n m)⦃σ⦄) ⇒⋆ n₁ := .trans' r₁.fst (.once .π1)
  simp only [substCom] at *
  cases hlet with | letin hn hm =>
  let ⟨w₁, w₂, _, rw₂, hA'⟩ := (soundCom hn σ τ hστ).ret_inv
  let ⟨m₁, _, m₂, _, _, r₂', _⟩ := (soundCom hm (w₁ +: σ) (w₂ +: τ) (semCtxt.cons hA' hστ)).fst
  have rlet : letin (n⦃τ⦄) (m⦃⇑ τ⦄) ⇒⋆ prod m₂ _ := calc
    _ ⇒⋆ letin (ret w₂) (m⦃⇑ τ⦄) := rw₂.let
    _ ⇒  m⦃w₂ +: τ⦄              := by rw [substUnion]; exact .ζ
    _ ⇒⋆ prod m₂ _               := r₂'
  let ⟨_, rprod₁, rprod₂⟩ := confluence r₂ rlet
  rw [← rprod₂.prod_inv] at rprod₁; injection rprod₁.prod_inv with e₁ e₂; subst e₁ e₂
  clear rlet rprod₁ rprod₂
  have r₂' : letin (n⦃τ⦄) (fst (m⦃⇑ τ⦄)) ⇒⋆ n₂ := calc
    _ ⇒⋆ letin (ret w₂) (fst (m⦃⇑ τ⦄)) := rw₂.let
    _ ⇒  fst (m⦃⇑ τ⦄⦃w₂⦄)              := .ζ
    _ =  fst (m⦃w₂ +: τ⦄)              := by rw [← substUnion]
    _ ⇒⋆ fst (prod n₂ _)               := r₂'.fst
    _ ⇒  n₂                            := .π1
  exact ℰ.bwds r₁' r₂' hB₁

theorem sndLet {Γ n m B₁ B₂}
  (hlet : Γ ⊢ letin n m ∶ Prod B₁ B₂) :
  Γ ⊨ snd (letin n m) ~ letin n (snd m) ∶ B₂ := by
  intro σ τ hστ
  let ⟨_, n₁, _, n₂, r₁, r₂, hB₂⟩ := (soundCom hlet σ τ hστ).snd
  have r₁' : snd ((letin n m)⦃σ⦄) ⇒⋆ n₁ := .trans' r₁.snd (.once .π2)
  simp only [substCom] at *
  cases hlet with | letin hn hm =>
  let ⟨w₁, w₂, _, rw₂, hA'⟩ := (soundCom hn σ τ hστ).ret_inv
  let ⟨m₁, _, m₂, _, _, r₂', _⟩ := (soundCom hm (w₁ +: σ) (w₂ +: τ) (semCtxt.cons hA' hστ)).fst
  have rlet : letin (n⦃τ⦄) (m⦃⇑ τ⦄) ⇒⋆ prod m₂ _ := calc
    _ ⇒⋆ letin (ret w₂) (m⦃⇑ τ⦄) := rw₂.let
    _ ⇒  m⦃w₂ +: τ⦄              := by rw [substUnion]; exact .ζ
    _ ⇒⋆ prod m₂ _               := r₂'
  let ⟨_, rprod₁, rprod₂⟩ := confluence r₂ rlet
  rw [← rprod₂.prod_inv] at rprod₁; injection rprod₁.prod_inv with e₁ e₂; subst e₁ e₂
  clear rlet rprod₁ rprod₂
  have r₂' : letin (n⦃τ⦄) (snd (m⦃⇑ τ⦄)) ⇒⋆ n₂ := calc
    _ ⇒⋆ letin (ret w₂) (snd (m⦃⇑ τ⦄)) := rw₂.let
    _ ⇒  snd (m⦃⇑ τ⦄⦃w₂⦄)              := .ζ
    _ =  snd (m⦃w₂ +: τ⦄)              := by rw [← substUnion]
    _ ⇒⋆ snd (prod _ n₂)               := r₂'.snd
    _ ⇒  n₂                            := .π2
  exact ℰ.bwds r₁' r₂' hB₂

theorem letCase {Γ v m₁ m₂ n A} {B : ComType}
  (hcase : Γ ⊢ case v m₁ m₂ ∶ F A)
  (hn : Γ ∷ A ⊢ n ∶ B) :
  Γ ⊨ letin (case v m₁ m₂) n
    ~ case v (letin m₁ (renameCom (lift succ) n)) (letin m₂ (renameCom (lift succ) n)) ∶ B := by
  intro σ τ hστ
  sorry

theorem appCase {Γ v w m₁ m₂ A B}
  (hcase : Γ ⊢ case v m₁ m₂ ∶ Arr A B)
  (hw : Γ ⊢ w ∶ A) :
  Γ ⊨ app (case v m₁ m₂) w ~ case v (app m₁ (renameVal succ w)) (app m₂ (renameVal succ w)) ∶ B := by
  intro σ τ hστ
  let ⟨n₁, n₂, r₁, r₂, hB₁⟩ := (soundCom hcase σ τ hστ).lam_inv
  have r₁' : app ((case v m₁ m₂)⦃σ⦄) (w⦃σ⦄) ⇒⋆ n₁⦃w⦃σ⦄⦄ := .trans' r₁.app (.once .β)
  simp only [substCom] at *
  cases hcase with | case hv hm₁ hm₂ =>
  let hv := soundVal hv σ τ hστ; unfold 𝒱 at hv
  match hv with
  | .inl ⟨v₁, v₂, hA₁, e₁, e₂⟩ =>
    rw [e₂]; rw [e₂] at r₂
    let ⟨_, _, _, r₂', hB₂⟩ := (soundCom hm₁ (v₁ +: σ) (v₂ +: τ) (semCtxt.cons hA₁ hστ)).lam_inv
    let ⟨_, rlam₁, r'⟩ := confluence r₂ (.once .ιl); rw [← substUnion] at r'
    let ⟨_, rlam₂, r'⟩ := confluence r₂' r'; rw [← rlam₂.lam_inv] at r'
    injection Evals.lam_inv (.trans' rlam₁ r') with en₂; subst en₂
    clear rlam₁ rlam₂ r' r₁; clear r'
    have r₂' :
      case (.inl v₂) (app (m₁⦃⇑ τ⦄) (renameVal succ w⦃⇑ τ⦄)) (app (m₂⦃⇑ τ⦄) (renameVal succ w⦃⇑ τ⦄))
        ⇒⋆ n₂⦃w⦃τ⦄⦄ := calc
      _ ⇒  app (m₁⦃⇑ τ⦄) (renameVal succ w⦃⇑ τ⦄) ⦃v₂⦄ := .ιl
      _ =  app (m₁⦃v₂ +: τ⦄) (w⦃τ⦄)
        := by simp only [substCom]; rw [← substUnion, ← renameUpSubstVal, ← substDropVal]
      _ ⇒⋆ app (lam n₂) (w⦃τ⦄) := r₂'.app
      _ ⇒  n₂⦃w⦃τ⦄⦄ := .β
    exact ℰ.bwds r₁' r₂' (hB₁ _ _ (soundVal hw σ τ hστ))
  | .inr ⟨v₁, v₂, hA₂, e₁, e₂⟩ =>
    rw [e₂]; rw [e₂] at r₂
    let ⟨_, _, _, r₂', hB₂⟩ := (soundCom hm₂ (v₁ +: σ) (v₂ +: τ) (semCtxt.cons hA₂ hστ)).lam_inv
    let ⟨_, rlam₁, r'⟩ := confluence r₂ (.once .ιr); rw [← substUnion] at r'
    let ⟨_, rlam₂, r'⟩ := confluence r₂' r'; rw [← rlam₂.lam_inv] at r'
    injection Evals.lam_inv (.trans' rlam₁ r') with en₂; subst en₂
    clear rlam₁ rlam₂ r' r₁; clear r'
    have r₂' :
      case (.inr v₂) (app (m₁⦃⇑ τ⦄) (renameVal succ w⦃⇑ τ⦄)) (app (m₂⦃⇑ τ⦄) (renameVal succ w⦃⇑ τ⦄))
        ⇒⋆ n₂⦃w⦃τ⦄⦄ := calc
      _ ⇒  app (m₂⦃⇑ τ⦄) (renameVal succ w⦃⇑ τ⦄) ⦃v₂⦄ := .ιr
      _ =  app (m₂⦃v₂ +: τ⦄) (w⦃τ⦄)
        := by simp only [substCom]; rw [← substUnion, ← renameUpSubstVal, ← substDropVal]
      _ ⇒⋆ app (lam n₂) (w⦃τ⦄) := r₂'.app
      _ ⇒  n₂⦃w⦃τ⦄⦄ := .β
    exact ℰ.bwds r₁' r₂' (hB₁ _ _ (soundVal hw σ τ hστ))

theorem fstCase {Γ v m₁ m₂ B₁ B₂}
  (hcase : Γ ⊢ case v m₁ m₂ ∶ Prod B₁ B₂) :
  Γ ⊨ fst (case v m₁ m₂) ~ case v (fst m₁) (fst m₂) ∶ B₁ := by
  intro σ τ hστ
  let ⟨n₁, _, n₂, _, r₁, r₂, hB₁⟩ := (soundCom hcase σ τ hστ).fst
  have r₁' : fst ((case v m₁ m₂)⦃σ⦄) ⇒⋆ n₁ := .trans' r₁.fst (.once .π1)
  simp only [substCom] at *
  cases hcase with | case hv hm₁ hm₂ =>
  let hv := soundVal hv σ τ hστ; unfold 𝒱 at hv
  match hv with
  | .inl ⟨v₁, v₂, hA₁, e₁, e₂⟩ =>
    rw [e₂]; rw [e₂] at r₂
    let ⟨_, _, _, _, _, r₂', _⟩ := (soundCom hm₁ (v₁ +: σ) (v₂ +: τ) (semCtxt.cons hA₁ hστ)).fst
    let ⟨_, rprod₁, r'⟩ := confluence r₂ (.once .ιl); rw [← substUnion] at r'
    let ⟨_, rprod₂, r'⟩ := confluence r₂' r'; rw [← rprod₂.prod_inv] at r'
    injection Evals.prod_inv (.trans' rprod₁ r') with en₁ en₂; subst en₁ en₂
    clear rprod₁ rprod₂ r' r₁; clear r'
    have r₂' :
      case (inl v₂) (fst (m₁⦃⇑ τ⦄)) (fst (m₂⦃⇑ τ⦄)) ⇒⋆ n₂ := calc
      _ ⇒  fst (m₁⦃⇑ τ⦄)⦃v₂⦄ := .ιl
      _ =  fst (m₁⦃v₂ +: τ⦄) := by simp only [substCom]; rw [← substUnion]
      _ ⇒⋆ fst (prod n₂ _)   := r₂'.fst
      _ ⇒ n₂                 := .π1
    exact ℰ.bwds r₁' r₂' hB₁
  | .inr ⟨v₁, v₂, hA₂, e₁, e₂⟩ =>
    rw [e₂]; rw [e₂] at r₂
    let ⟨_, _, _, _, _, r₂', _⟩ := (soundCom hm₂ (v₁ +: σ) (v₂ +: τ) (semCtxt.cons hA₂ hστ)).fst
    let ⟨_, rprod₁, r'⟩ := confluence r₂ (.once .ιr); rw [← substUnion] at r'
    let ⟨_, rprod₂, r'⟩ := confluence r₂' r'; rw [← rprod₂.prod_inv] at r'
    injection Evals.prod_inv (.trans' rprod₁ r') with en₁ en₂; subst en₁ en₂
    clear rprod₁ rprod₂ r' r₁; clear r'
    have r₂' :
      case (inr v₂) (fst (m₁⦃⇑ τ⦄)) (fst (m₂⦃⇑ τ⦄)) ⇒⋆ n₂ := calc
      _ ⇒  fst (m₂⦃⇑ τ⦄)⦃v₂⦄ := .ιr
      _ =  fst (m₂⦃v₂ +: τ⦄) := by simp only [substCom]; rw [← substUnion]
      _ ⇒⋆ fst (prod n₂ _)   := r₂'.fst
      _ ⇒ n₂                 := .π1
    exact ℰ.bwds r₁' r₂' hB₁

theorem sndCase {Γ v m₁ m₂ B₁ B₂}
  (hcase : Γ ⊢ case v m₁ m₂ ∶ Prod B₁ B₂) :
  Γ ⊨ snd (case v m₁ m₂) ~ case v (snd m₁) (snd m₂) ∶ B₂ := by
  intro σ τ hστ
  let ⟨_, n₁, _, n₂, r₁, r₂, hB₁⟩ := (soundCom hcase σ τ hστ).snd
  have r₁' : snd ((case v m₁ m₂)⦃σ⦄) ⇒⋆ n₁ := .trans' r₁.snd (.once .π2)
  simp only [substCom] at *
  cases hcase with | case hv hm₁ hm₂ =>
  let hv := soundVal hv σ τ hστ; unfold 𝒱 at hv
  match hv with
  | .inl ⟨v₁, v₂, hA₁, e₁, e₂⟩ =>
    rw [e₂]; rw [e₂] at r₂
    let ⟨_, _, _, _, _, r₂', _⟩ := (soundCom hm₁ (v₁ +: σ) (v₂ +: τ) (semCtxt.cons hA₁ hστ)).snd
    let ⟨_, rprod₁, r'⟩ := confluence r₂ (.once .ιl); rw [← substUnion] at r'
    let ⟨_, rprod₂, r'⟩ := confluence r₂' r'; rw [← rprod₂.prod_inv] at r'
    injection Evals.prod_inv (.trans' rprod₁ r') with en₁ en₂; subst en₁ en₂
    clear rprod₁ rprod₂ r' r₁; clear r'
    have r₂' :
      case (inl v₂) (snd (m₁⦃⇑ τ⦄)) (snd (m₂⦃⇑ τ⦄)) ⇒⋆ n₂ := calc
      _ ⇒  snd (m₁⦃⇑ τ⦄)⦃v₂⦄ := .ιl
      _ =  snd (m₁⦃v₂ +: τ⦄) := by simp only [substCom]; rw [← substUnion]
      _ ⇒⋆ snd (prod _ n₂)   := r₂'.snd
      _ ⇒ n₂                 := .π2
    exact ℰ.bwds r₁' r₂' hB₁
  | .inr ⟨v₁, v₂, hA₂, e₁, e₂⟩ =>
    rw [e₂]; rw [e₂] at r₂
    let ⟨_, _, _, _, _, r₂', _⟩ := (soundCom hm₂ (v₁ +: σ) (v₂ +: τ) (semCtxt.cons hA₂ hστ)).snd
    let ⟨_, rprod₁, r'⟩ := confluence r₂ (.once .ιr); rw [← substUnion] at r'
    let ⟨_, rprod₂, r'⟩ := confluence r₂' r'; rw [← rprod₂.prod_inv] at r'
    injection Evals.prod_inv (.trans' rprod₁ r') with en₁ en₂; subst en₁ en₂
    clear rprod₁ rprod₂ r' r₁; clear r'
    have r₂' :
      case (inr v₂) (snd (m₁⦃⇑ τ⦄)) (snd (m₂⦃⇑ τ⦄)) ⇒⋆ n₂ := calc
      _ ⇒  snd (m₂⦃⇑ τ⦄)⦃v₂⦄ := .ιr
      _ =  snd (m₂⦃v₂ +: τ⦄) := by simp only [substCom]; rw [← substUnion]
      _ ⇒⋆ snd (prod _ n₂)   := r₂'.snd
      _ ⇒ n₂                 := .π2
    exact ℰ.bwds r₁' r₂' hB₁
