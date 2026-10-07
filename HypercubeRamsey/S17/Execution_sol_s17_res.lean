import HypercubeRamsey.S17.Needs

namespace HypercubeRamsey.Lane_sol_s17_res

open Classical

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
variable {D : ListGateContext κ T k PT}

private theorem before_total (order : Pos T k → ℕ) {v w : Pos T k} (h : v ≠ w) :
    ListEvent.before order v w ∨ ListEvent.before order w v := by
  rcases lt_trichotomy (order v) (order w) with ho | ho | ho
  · exact Or.inl (Or.inl ho)
  · have hr : ListEvent.canonicalRank v ≠ ListEvent.canonicalRank w := by
      intro he
      apply h
      apply (Fintype.equivFin (Pos T k)).injective
      exact Fin.ext he
    rcases lt_or_gt_of_ne hr with hr | hr
    · exact Or.inl (Or.inr ⟨ho, hr⟩)
    · exact Or.inr (Or.inr ⟨ho.symm, hr⟩)
  · exact Or.inr (Or.inl ho)

theorem active_touch_unique (LE : ListEvent D.F) (order : Pos T k → ℕ)
    (events : Finset (Pos T k)) (s : Config D.F)
    {v w : Pos T k} (hv : v ∈ LE.active order events s)
    (hw : w ∈ LE.active order events s) {C : D.G.Cell}
    (hCv : C ∈ LE.scope v) (hCw : C ∈ LE.scope w) : v = w := by
  by_contra hne
  have hv' := (Finset.mem_filter.mp hv).2
  have hw' := (Finset.mem_filter.mp hw).2
  have hmeet : ¬ Disjoint (LE.scope v) (LE.scope w) := by
    intro h
    exact Finset.disjoint_left.mp h hCv hCw
  rcases before_total order hne with h | h
  · exact hw'.2.2 v hv'.1 h ⟨hne, hmeet⟩ hv'.2.1
  · exact hv'.2.2 w hw'.1 h ⟨Ne.symm hne, fun h => hmeet h.symm⟩ hw'.2.1

def Executed (LE : ListEvent D.F) (order : Pos T k → ℕ)
    (events : Finset (Pos T k)) (pools : ∀ C, D.F.Pool C)
    (tapes : ∀ C, ℕ → TapeEntry D.F C) {Ts : ℕ} (o : Pos T k × Fin Ts) : Prop :=
  o.1 ∈ LE.active order events (LE.runRounds o.2.val order events pools tapes).1

noncomputable def priorExecutions (LE : ListEvent D.F) (Ts n : ℕ)
    (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C, D.F.Pool C) (tapes : ∀ C, ℕ → TapeEntry D.F C)
    (C : D.G.Cell) : Finset (Pos T k × Fin Ts) :=
  Finset.univ.filter fun o => Executed LE order events pools tapes o ∧
    o.2.val < n ∧ C ∈ LE.scope o.1

theorem run_state (LE : ListEvent D.F) (order : Pos T k → ℕ)
    (events : Finset (Pos T k)) (pools : ∀ C, D.F.Pool C)
    (tapes : ∀ C, ℕ → TapeEntry D.F C) (n : ℕ) (C : D.G.Cell) :
    (LE.runRounds n order events pools tapes).1 C =
      tapes C ((LE.runRounds n order events pools tapes).2 C) (pools C) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show LE.runRounds (n + 1) order events pools tapes =
      LE.round order events pools tapes (LE.runRounds n order events pools tapes).1
        (LE.runRounds n order events pools tapes).2 by rfl]
    simp only [ListEvent.round]
    split_ifs <;> simp_all

theorem run_counter_le (LE : ListEvent D.F) (order : Pos T k → ℕ)
    (events : Finset (Pos T k)) (pools : ∀ C, D.F.Pool C)
    (tapes : ∀ C, ℕ → TapeEntry D.F C) (n : ℕ) (C : D.G.Cell) :
    (LE.runRounds n order events pools tapes).2 C ≤ n := by
  induction n with
  | zero => exact le_refl _
  | succ n ih =>
    rw [show LE.runRounds (n + 1) order events pools tapes =
      LE.round order events pools tapes (LE.runRounds n order events pools tapes).1
        (LE.runRounds n order events pools tapes).2 by rfl]
    simp only [ListEvent.round]
    split_ifs <;> omega

private theorem priorExecutions_step (LE : ListEvent D.F) (Ts n : ℕ)
    (hn : n < Ts) (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C, D.F.Pool C) (tapes : ∀ C, ℕ → TapeEntry D.F C) (C : D.G.Cell) :
    (priorExecutions LE Ts (n + 1) order events pools tapes C).card =
      (priorExecutions LE Ts n order events pools tapes C).card +
      if ∃ v ∈ LE.active order events (LE.runRounds n order events pools tapes).1,
        C ∈ LE.scope v then 1 else 0 := by
  let A := priorExecutions LE Ts n order events pools tapes C
  let B := Finset.univ.filter fun o : Pos T k × Fin Ts =>
    Executed LE order events pools tapes o ∧ o.2.val = n ∧ C ∈ LE.scope o.1
  have hEq : priorExecutions LE Ts (n + 1) order events pools tapes C = A ∪ B := by
    ext o
    simp only [priorExecutions, A, B, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_union]
    constructor
    · rintro ⟨he, hr, hC⟩
      by_cases hlt : o.2.val < n
      · exact Or.inl ⟨he, hlt, hC⟩
      · exact Or.inr ⟨he, by omega, hC⟩
    · rintro (⟨he, hr, hC⟩ | ⟨he, hr, hC⟩) <;> exact ⟨he, by omega, hC⟩
  have hDis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro o ho hp
    have ha := (Finset.mem_filter.mp ho).2.2.1
    have hb := (Finset.mem_filter.mp hp).2.2.1
    omega
  rw [hEq, Finset.card_union_of_disjoint hDis]
  congr 1
  by_cases ht : ∃ v ∈ LE.active order events
      (LE.runRounds n order events pools tapes).1, C ∈ LE.scope v
  · obtain ⟨v, hv, hCv⟩ := ht
    rw [if_pos ⟨v, hv, hCv⟩]
    have hsingleton : B = {(v, ⟨n, hn⟩)} := by
      ext o
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · rintro ⟨ho, hr, hCo⟩
        have hactive : o.1 ∈ LE.active order events
            (LE.runRounds n order events pools tapes).1 := by
          simpa only [Executed, hr] using ho
        exact Prod.ext (active_touch_unique LE order events _ hactive hv hCo hCv)
          (Fin.ext hr)
      · rintro rfl
        exact ⟨hv, rfl, hCv⟩
    simp only [hsingleton, Finset.card_singleton]
  · rw [if_neg ht]
    have he : B = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro o ho
      obtain ⟨ho, hr, hCo⟩ := (Finset.mem_filter.mp ho).2
      apply ht
      exact ⟨o.1, by simpa only [Executed, hr] using ho, hCo⟩
    simp [he]

theorem run_counter_eq (LE : ListEvent D.F) (Ts : ℕ)
    (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C, D.F.Pool C) (tapes : ∀ C, ℕ → TapeEntry D.F C)
    (n : ℕ) (hn : n ≤ Ts) (C : D.G.Cell) :
    (LE.runRounds n order events pools tapes).2 C =
      (priorExecutions LE Ts n order events pools tapes C).card := by
  induction n with
  | zero => simp [ListEvent.runRounds, priorExecutions]
  | succ n ih =>
    rw [priorExecutions_step LE Ts n (by omega) order events pools tapes C]
    have he := ih (by omega)
    rw [show LE.runRounds (n + 1) order events pools tapes =
      LE.round order events pools tapes (LE.runRounds n order events pools tapes).1
        (LE.runRounds n order events pools tapes).2 by rfl]
    simp only [ListEvent.round]
    split_ifs <;> simp_all

theorem enumeration_filter_card {α : Type*} [DecidableEq α] {m : ℕ}
    (f : Fin m → α) (hf : Function.Injective f) (s : Finset α)
    (hs : Finset.univ.image f = s) (p : α → Prop) :
    (Finset.univ.filter fun j => p (f j)).card = (s.filter p).card := by
  classical
  rw [← hs, Finset.filter_image, Finset.card_image_of_injective _ hf]

end HypercubeRamsey.Lane_sol_s17_res
