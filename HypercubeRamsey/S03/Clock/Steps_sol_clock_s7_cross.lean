import HypercubeRamsey.S03.Clock.Steps_sol_clock_s7

set_option autoImplicit false

namespace HypercubeRamsey.Lane_sol_clock_s7

open Clock

private theorem project_runGreedy {T : ℕ} {R : Type*} [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (S : Finset R) (L : Finset (Fin g))
    (events : List (ClockCandidate T R g Ω))
    (hsep : Separated S L (runGreedy ξ events)) :
    projectState S (runGreedy ξ events) =
      runGreedy ξ (events.filter (fun e => e.1 ∉ S ∧ e.2.1 ∉ L)) := by
  classical
  have hempty : projectState S (emptyGreedyState (g := g) (Ω := Ω)) = emptyGreedyState := by
    unfold projectState emptyGreedyState
    congr 1
    funext a
    simp
  simpa only [runGreedy, hempty] using
    project_fold_eq_outside_fold ξ S L events emptyGreedyState hsep

private theorem append_label_free {T : ℕ} {R : Type*} [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (pre suffix : List (ClockCandidate T R g Ω))
    (y : Fin g) (hfree : ¬ labelUsed (runGreedy ξ (pre ++ suffix)) y) :
    ¬ labelUsed (runGreedy ξ pre) y := by
  rintro ⟨a, o, ha⟩
  apply hfree
  refine ⟨a, o, ?_⟩
  simpa [runGreedy, List.foldl_append] using
    runGreedy_preserves_existing_assignment ξ suffix (runGreedy ξ pre) a (y, o) ha

private theorem append_row_free {T : ℕ} {R : Type*} [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (pre suffix : List (ClockCandidate T R g Ω))
    (a : R) (hfree : (runGreedy ξ (pre ++ suffix)).assignment a = none) :
    (runGreedy ξ pre).assignment a = none := by
  classical
  by_contra ha
  have hpres := runGreedy_preserves_assignment ξ suffix (runGreedy ξ pre) a ha
  apply hpres
  simpa [runGreedy, List.foldl_append] using hfree

private theorem background_through_event_append {T : ℕ} {R : Type*}
    [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (S : Finset R) (L : Finset (Fin g))
    (pre suffix : List (ClockCandidate T R g Ω)) (e : ClockCandidate T R g Ω)
    (hevents : clockEventList ξ = pre ++ e :: suffix)
    (htimes : ∀ f ∈ pre, f.2.2.1.val ≤ e.2.2.1.val) :
    runGreedy ξ ((clockEventList ξ).filter (fun f =>
        f.1 ∉ S ∧ f.2.1 ∉ L ∧ f.2.2.1.val < e.2.2.1.val + 1)) =
      runGreedy ξ ((pre.filter (fun f => f.1 ∉ S ∧ f.2.1 ∉ L)) ++
        ((e :: suffix).filter (fun f =>
          f.1 ∉ S ∧ f.2.1 ∉ L ∧ f.2.2.1.val < e.2.2.1.val + 1))) := by
  classical
  have hprefix : pre.filter (fun f =>
        f.1 ∉ S ∧ f.2.1 ∉ L ∧ f.2.2.1.val < e.2.2.1.val + 1) =
      pre.filter (fun f => f.1 ∉ S ∧ f.2.1 ∉ L) := by
    apply List.filter_congr
    intro f hf
    simp [Nat.lt_succ_iff.mpr (htimes f hf)]
  rw [hevents, List.filter_append, hprefix]

/-- A target row cannot send an early ordinary arrival to a free outside label. -/
theorem target_row_cross_arrival_forbidden {T : ℕ} {R : Type*}
    [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (S : Finset R) (o : ∀ a, Ω a)
    (lab : ∀ a, Ω a → Fin g) (times : R → Fin T)
    (htarget : ∀ a ∈ S, (greedyMatching ξ).assignment a = some (lab a (o a), o a))
    (hclock : ∀ a ∈ S, ξ (a, lab a (o a)) = .tick (times a) (o a))
    (a : R) (y : Fin g) (t : Fin T) (mark : Ω a)
    (ha : a ∈ S) (hy : y ∉ S.image (fun b => lab b (o b)))
    (ht : t.val < (times a).val) (harrival : ξ (a, y) = .tick t mark)
    (hfree : ¬ labelUsed (runGreedy ξ ((clockEventList ξ).filter (fun f =>
      f.1 ∉ S ∧ f.2.1 ∉ S.image (fun b => lab b (o b)) ∧ f.2.2.1.val < t.val + 1))) y) :
    False := by
  classical
  let L := S.image fun b => lab b (o b)
  let e : ClockCandidate T R g Ω := ⟨a, y, t, mark⟩
  have he : e ∈ clockEventList ξ :=
    (clockEventList_mem_iff_p_clock_r4 ξ e).mpr harrival
  obtain ⟨pre, suffix, hevents⟩ := List.mem_iff_append.mp he
  have hsort := clockEventList_sorted ξ
  rw [hevents, List.pairwise_append] at hsort
  have htimes : ∀ f ∈ pre, f.2.2.1.val ≤ t.val := by
    intro f hf
    exact tick_le_of_priority_le f e (hsort.2.2 f hf e (by simp))
  have hsep : Separated S L (greedyMatching ξ) :=
    target_matching_separated ξ S o lab htarget
  have hprefixsep : Separated S L (runGreedy ξ pre) := by
    apply separated_before_fold ξ (e :: suffix) S L
    simpa [runGreedy, greedyMatching, hevents, List.foldl_append] using hsep
  have hproject := project_runGreedy ξ S L pre hprefixsep
  have hrow : (runGreedy ξ pre).assignment a = none := by
    apply prefix_target_row_free ξ pre (e :: suffix) a (lab a (o a)) (times a) (o a)
    · simpa [greedyMatching, hevents] using htarget a ha
    · exact hclock a ha
    · intro hmem
      have hle := htimes ⟨a, lab a (o a), times a, o a⟩ hmem
      exact (not_le_of_gt ht) hle
  have hbgfree : ¬ labelUsed
      (runGreedy ξ (pre.filter (fun f => f.1 ∉ S ∧ f.2.1 ∉ L))) y := by
    apply append_label_free ξ _
      ((e :: suffix).filter (fun f => f.1 ∉ S ∧ f.2.1 ∉ L ∧ f.2.2.1.val < t.val + 1)) y
    rw [← background_through_event_append ξ S L pre suffix e hevents htimes]
    exact hfree
  have hlabel : ¬ labelUsed (runGreedy ξ pre) y := by
    intro hused
    apply hbgfree
    rw [← hproject]
    exact (labelUsed_projectState S L _ hprefixsep y hy).mpr hused
  apply crossing_arrival_forbidden ξ S L pre suffix e
  · simpa [greedyMatching, hevents] using hsep
  · exact harrival
  · exact hrow
  · exact hlabel
  · intro hcross
    exact hy (hcross.mp ha)

/-- A target label cannot receive an early ordinary arrival from a free outside row. -/
theorem target_label_cross_arrival_forbidden {T : ℕ} {R : Type*}
    [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ξ : ClockField T R g Ω) (S : Finset R) (o : ∀ a, Ω a)
    (lab : ∀ a, Ω a → Fin g) (times : R → Fin T)
    (htarget : ∀ a ∈ S, (greedyMatching ξ).assignment a = some (lab a (o a), o a))
    (hclock : ∀ a ∈ S, ξ (a, lab a (o a)) = .tick (times a) (o a))
    (a b : R) (t : Fin T) (mark : Ω b)
    (ha : a ∈ S) (hb : b ∉ S)
    (ht : t.val < (times a).val) (harrival : ξ (b, lab a (o a)) = .tick t mark)
    (hfree : (runGreedy ξ ((clockEventList ξ).filter (fun f =>
      f.1 ∉ S ∧ f.2.1 ∉ S.image (fun c => lab c (o c)) ∧ f.2.2.1.val < t.val + 1))).assignment b = none) :
    False := by
  classical
  let L := S.image fun c => lab c (o c)
  let e : ClockCandidate T R g Ω := ⟨b, lab a (o a), t, mark⟩
  have he : e ∈ clockEventList ξ :=
    (clockEventList_mem_iff_p_clock_r4 ξ e).mpr harrival
  obtain ⟨pre, suffix, hevents⟩ := List.mem_iff_append.mp he
  have hsort := clockEventList_sorted ξ
  rw [hevents, List.pairwise_append] at hsort
  have htimes : ∀ f ∈ pre, f.2.2.1.val ≤ t.val := by
    intro f hf
    exact tick_le_of_priority_le f e (hsort.2.2 f hf e (by simp))
  have hsep : Separated S L (greedyMatching ξ) :=
    target_matching_separated ξ S o lab htarget
  have hprefixsep : Separated S L (runGreedy ξ pre) := by
    apply separated_before_fold ξ (e :: suffix) S L
    simpa [runGreedy, greedyMatching, hevents, List.foldl_append] using hsep
  have hproject := project_runGreedy ξ S L pre hprefixsep
  have htargetfree : (runGreedy ξ pre).assignment a = none := by
    apply prefix_target_row_free ξ pre (e :: suffix) a (lab a (o a)) (times a) (o a)
    · simpa [greedyMatching, hevents] using htarget a ha
    · exact hclock a ha
    · intro hmem
      have hle := htimes ⟨a, lab a (o a), times a, o a⟩ hmem
      exact (not_le_of_gt ht) hle
  have hlabel : ¬ labelUsed (runGreedy ξ pre) (lab a (o a)) := by
    apply prefix_target_label_free ξ pre (e :: suffix) a (lab a (o a))
    · intro c oc hc
      apply greedyMatching_label_injective ξ c a (lab a (o a)) oc (o a)
      · simpa [greedyMatching, hevents] using hc
      · exact htarget a ha
    · exact htargetfree
  have hrowbg :
      (runGreedy ξ (pre.filter (fun f => f.1 ∉ S ∧ f.2.1 ∉ L))).assignment b = none := by
    apply append_row_free ξ _
      ((e :: suffix).filter (fun f => f.1 ∉ S ∧ f.2.1 ∉ L ∧ f.2.2.1.val < t.val + 1)) b
    rw [← background_through_event_append ξ S L pre suffix e hevents htimes]
    exact hfree
  have hrow : (runGreedy ξ pre).assignment b = none := by
    rw [← hproject] at hrowbg
    simpa [projectState, hb] using hrowbg
  apply crossing_arrival_forbidden ξ S L pre suffix e
  · simpa [greedyMatching, hevents] using hsep
  · exact harrival
  · exact hrow
  · exact hlabel
  · intro hcross
    exact hb (hcross.mpr (Finset.mem_image.mpr ⟨a, ha, rfl⟩))

end HypercubeRamsey.Lane_sol_clock_s7
