import HypercubeRamsey.S03.Clock.Steps_sol_clock_s7_cutoff

set_option autoImplicit false

namespace HypercubeRamsey.Lane_sol_clock_s7

open Clock

def overlay {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*}
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) : ClockField T R g Ω := fun e => (ins e).getD (ξ e)

noncomputable def backgroundAt {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (S : Finset R) (L : Finset (Fin g)) (h : ℕ) :
    GreedyState R g Ω := edgeMatchingThrough (overlay ins ξ) (backgroundEdges S L) h

theorem backgroundAt_eq {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (S : Finset R) (L : Finset (Fin g)) (h : ℕ) :
    backgroundAt ins ξ S L h = runGreedy (overlay ins ξ)
      ((clockEventList (overlay ins ξ)).filter
        (fun e => e.1 ∉ S ∧ e.2.1 ∉ L ∧ e.2.2.1.val < h)) := by
  classical
  simp [backgroundAt, edgeMatchingThrough, backgroundEdges, List.filter_filter,
    and_assoc, and_left_comm, and_comm, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

theorem backgroundAt_eq_of_agree {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ ξ' : ClockField T R g Ω) (S : Finset R) (L : Finset (Fin g)) (h : ℕ)
    (hagree : ∀ e ∈ backgroundEdges S L, ξ e = ξ' e) :
    backgroundAt ins ξ S L h = backgroundAt ins ξ' S L h := by
  classical
  have h := runGreedy_filter_edges_eq (overlay ins ξ) (overlay ins ξ') (backgroundEdges S L) h
    (by intro e he; simp [overlay, hagree e he])
  simpa [backgroundAt, edgeMatchingThrough, List.filter_filter, Bool.and_comm] using h

def crossForbiddenTimes {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (S : Finset R) (L : Finset (Fin g))
    (o : ∀ a, Ω a) (lab : ∀ a, Ω a → Fin g) (times : R → Fin T) :
    CrossIndex S L → Fin T → Prop
  | .inl (a, y), t => ins (a.1, y.1) = none ∧ t.val < (times a.1).val ∧
      ¬ labelUsed (backgroundAt ins ξ S L (t.val + 1)) y.1
  | .inr (a, b), t => ins (b.1, lab a.1 (o a.1)) = none ∧ t.val < (times a.1).val ∧
      (backgroundAt ins ξ S L (t.val + 1)).assignment b.1 = none

theorem crossForbiddenTimes_downward {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (S : Finset R) (L : Finset (Fin g))
    (o : ∀ a, Ω a) (lab : ∀ a, Ω a → Fin g) (times : R → Fin T)
    (c : CrossIndex S L) :
    ∀ i j, i.val ≤ j.val → crossForbiddenTimes ins ξ S L o lab times c j →
      crossForbiddenTimes ins ξ S L o lab times c i := by
  intro i j hij hj
  cases c with
  | inl p =>
    obtain ⟨hins, ht, hfree⟩ := hj
    refine ⟨hins, lt_of_le_of_lt hij ht, ?_⟩
    exact edgeMatchingThrough_label_free (overlay ins ξ) (backgroundEdges S L)
      (i.val + 1) (j.val + 1) (Nat.add_le_add_right hij 1) p.2.1 hfree
  | inr p =>
    obtain ⟨hins, ht, hfree⟩ := hj
    refine ⟨hins, lt_of_le_of_lt hij ht, ?_⟩
    exact edgeMatchingThrough_row_free (overlay ins ξ) (backgroundEdges S L)
      (i.val + 1) (j.val + 1) (Nat.add_le_add_right hij 1) p.2.1 hfree

noncomputable def crossDynamicCutoff {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (S : Finset R) (L : Finset (Fin g))
    (o : ∀ a, Ω a) (lab : ∀ a, Ω a → Fin g) (times : R → Fin T)
    (c : CrossIndex S L) : ℕ := by
  classical
  exact (Finset.univ.filter (crossForbiddenTimes ins ξ S L o lab times c)).card

theorem crossDynamicCutoff_le {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (S : Finset R) (L : Finset (Fin g))
    (o : ∀ a, Ω a) (lab : ∀ a, Ω a → Fin g) (times : R → Fin T)
    (c : CrossIndex S L) : crossDynamicCutoff ins ξ S L o lab times c ≤ T := by
  classical
  simpa [crossDynamicCutoff] using
    Finset.card_le_card (Finset.filter_subset
      (p := crossForbiddenTimes ins ξ S L o lab times c) Finset.univ)

/-- Realizing all prescribed matches forbids first arrivals throughout each dynamic cross-edge cutoff. -/
theorem target_matching_no_early_cross {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (S : Finset R) (o : ∀ a, Ω a)
    (lab : ∀ a, Ω a → Fin g) (times : R → Fin T)
    (htarget : ∀ a ∈ S, (greedyMatching (overlay ins ξ)).assignment a = some (lab a (o a), o a))
    (hclock : ∀ a ∈ S, overlay ins ξ (a, lab a (o a)) = .tick (times a) (o a))
    (c : CrossIndex S (S.image fun a => lab a (o a))) :
    NoEarlyArrival (crossDynamicCutoff ins ξ S (S.image fun a => lab a (o a)) o lab times c)
      (ξ (crossEdge S (S.image fun a => lab a (o a)) o lab c)) := by
  classical
  let L := S.image fun a => lab a (o a)
  cases hx : ξ (crossEdge S L o lab c) with
  | noArrival => simp [NoEarlyArrival]
  | tick t mark =>
    change crossDynamicCutoff ins ξ S L o lab times c ≤ t.val
    by_contra hle
    have htcut : t.val < crossDynamicCutoff ins ξ S L o lab times c := Nat.lt_of_not_ge hle
    have hH := (fin_initial_segment (crossForbiddenTimes ins ξ S L o lab times c)
      (crossForbiddenTimes_downward ins ξ S L o lab times c) t).mpr htcut
    cases c with
    | inl p =>
      obtain ⟨hins, ht, hfree⟩ := hH
      have harr : overlay ins ξ (p.1.1, p.2.1) = .tick t mark := by
        simpa [overlay, hins, crossEdge] using hx
      rw [backgroundAt_eq] at hfree
      exact target_row_cross_arrival_forbidden (overlay ins ξ) S o lab times htarget hclock
        p.1.1 p.2.1 t mark p.1.2 p.2.2 ht harr hfree
    | inr p =>
      obtain ⟨hins, ht, hfree⟩ := hH
      have harr : overlay ins ξ (p.2.1, lab p.1.1 (o p.1.1)) = .tick t mark := by
        simpa [overlay, hins, crossEdge] using hx
      rw [backgroundAt_eq] at hfree
      exact target_label_cross_arrival_forbidden (overlay ins ξ) S o lab times htarget hclock
        p.1.1 p.2.1 t mark p.1.2 p.2.2 ht harr hfree

theorem crossDynamicCutoff_eq_of_agree {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ ξ' : ClockField T R g Ω) (S : Finset R) (L : Finset (Fin g))
    (o : ∀ a, Ω a) (lab : ∀ a, Ω a → Fin g) (times : R → Fin T)
    (hagree : ∀ e ∈ backgroundEdges S L, ξ e = ξ' e) (c : CrossIndex S L) :
    crossDynamicCutoff ins ξ S L o lab times c = crossDynamicCutoff ins ξ' S L o lab times c := by
  classical
  have hH : crossForbiddenTimes ins ξ S L o lab times c =
      crossForbiddenTimes ins ξ' S L o lab times c := by
    funext t
    cases c with
    | inl p =>
      simp only [crossForbiddenTimes]
      rw [backgroundAt_eq_of_agree ins ξ ξ' S L (t.val + 1) hagree]
    | inr p =>
      simp only [crossForbiddenTimes]
      rw [backgroundAt_eq_of_agree ins ξ ξ' S L (t.val + 1) hagree]
  unfold crossDynamicCutoff
  rw [hH]

noncomputable def targetCrossCutoff {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (S : Finset R) (o : ∀ a, Ω a)
    (lab : ∀ a, Ω a → Fin g) (times : R → Fin T) : RowLabel R g → ℕ :=
  extendCrossCutoff S (S.image fun a => lab a (o a)) o lab
    (crossDynamicCutoff ins ξ S (S.image fun a => lab a (o a)) o lab times)

theorem targetCrossCutoff_le {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (S : Finset R) (o : ∀ a, Ω a)
    (lab : ∀ a, Ω a → Fin g) (times : R → Fin T)
    (hInj : Set.InjOn (fun a => lab a (o a)) S) (e : RowLabel R g) :
    targetCrossCutoff ins ξ S o lab times e ≤ T := by
  classical
  by_cases he : ∃ c, crossEdge S (S.image fun a => lab a (o a)) o lab c = e
  · obtain ⟨c, rfl⟩ := he
    rw [targetCrossCutoff, extendCrossCutoff_apply _ _ _ _ hInj]
    exact crossDynamicCutoff_le ins ξ S _ o lab times c
  · rw [targetCrossCutoff, extendCrossCutoff, Function.extend_apply' _ _ e he]
    exact Nat.zero_le _

theorem target_matching_cross_survival {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (S : Finset R) (o : ∀ a, Ω a)
    (lab : ∀ a, Ω a → Fin g) (times : R → Fin T)
    (hInj : Set.InjOn (fun a => lab a (o a)) S)
    (htarget : ∀ a ∈ S, (greedyMatching (overlay ins ξ)).assignment a = some (lab a (o a), o a))
    (hclock : ∀ a ∈ S, overlay ins ξ (a, lab a (o a)) = .tick (times a) (o a)) :
    ∀ e, NoEarlyArrival (targetCrossCutoff ins ξ S o lab times e) (ξ e) := by
  classical
  intro e
  by_cases he : ∃ c, crossEdge S (S.image fun a => lab a (o a)) o lab c = e
  · obtain ⟨c, rfl⟩ := he
    rw [targetCrossCutoff, extendCrossCutoff_apply _ _ _ _ hInj]
    exact target_matching_no_early_cross ins ξ S o lab times htarget hclock c
  · rw [targetCrossCutoff, extendCrossCutoff, Function.extend_apply' _ _ e he]
    cases ξ e <;> simp [NoEarlyArrival]

end HypercubeRamsey.Lane_sol_clock_s7
