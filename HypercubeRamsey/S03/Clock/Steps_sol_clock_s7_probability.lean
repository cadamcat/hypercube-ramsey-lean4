import HypercubeRamsey.S03.Clock.Steps_sol_clock_s7_kernel
import HypercubeRamsey.S03.Clock.Steps_sol_clock_s7_absence
import HypercubeRamsey.S03.Clock.Steps_sol_clock_s7_integral
import HypercubeRamsey.S03.Clock.Steps_sol_clock_s7_bound

set_option autoImplicit false

namespace HypercubeRamsey.Lane_sol_clock_s7

open Clock Classical
open scoped BigOperators

noncomputable def fillBackground {T : ℕ} {R : Type*} [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} (D : Finset (RowLabel R g))
    (bg : ∀ e : {e // e ∈ D}, MeshClockValue T (Ω e.1.1)) : ClockField T R g Ω :=
  fun e => if he : e ∈ D then bg ⟨e, he⟩ else .noArrival

theorem targetCrossCutoff_fillBackground {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (S : Finset R) (o : ∀ a, Ω a)
    (lab : ∀ a, Ω a → Fin g) (times : R → Fin T) :
    targetCrossCutoff ins ξ S o lab times =
      targetCrossCutoff ins
        (fillBackground (backgroundEdges S (S.image fun a => lab a (o a))) (fun e => ξ e.1))
        S o lab times := by
  classical
  have hc : crossDynamicCutoff ins ξ S (S.image fun a => lab a (o a)) o lab times =
      crossDynamicCutoff ins
        (fillBackground (backgroundEdges S (S.image fun a => lab a (o a))) (fun e => ξ e.1))
        S (S.image fun a => lab a (o a)) o lab times := by
    funext c
    apply crossDynamicCutoff_eq_of_agree
    intro e he
    simp [fillBackground, he]
  unfold targetCrossCutoff
  rw [hc]

noncomputable def extendTargetTimes {T : ℕ} [Nonempty (Fin T)] {R : Type*} [DecidableEq R]
    (S : Finset R) (times : S → Fin T) : R → Fin T :=
  fun a => if ha : a ∈ S then times ⟨a, ha⟩ else Classical.choice inferInstance

theorem extendTargetTimes_on {T : ℕ} [Nonempty (Fin T)] {R : Type*} [DecidableEq R]
    (S : Finset R) (times : S → Fin T) (a : S) : extendTargetTimes S times a.1 = times a := by
  simp [extendTargetTimes, a.2]

theorem arrival_time_factor_le {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g)
    (S : Finset R) (o : ∀ a, Ω a) (times : R → Fin T) :
    ((∏ a ∈ S, (p a).w (o a)) *
      ∏ a ∈ S, survival δ (labMarg (p a) (lab a) (lab a (o a))) (times a).val * δ) ≤
      (∏ a ∈ S, (p a).w (o a)) * δ ^ S.card := by
  classical
  have hsurv0 (a : R) : 0 ≤ survival δ (labMarg (p a) (lab a) (lab a (o a))) (times a).val := by
    exact pow_nonneg (sub_nonneg.mpr
      (mul_le_one₀ hδ1 (labMarg_nonneg _ _ _) (labMarg_le_one _ _ _))) _
  have hsurv1 (a : R) : survival δ (labMarg (p a) (lab a) (lab a (o a))) (times a).val ≤ 1 := by
    apply pow_le_one₀
    · exact sub_nonneg.mpr (mul_le_one₀ hδ1 (labMarg_nonneg _ _ _) (labMarg_le_one _ _ _))
    · exact sub_le_self _ (mul_nonneg hδ0 (labMarg_nonneg _ _ _))
  have hp : 0 ≤ ∏ a ∈ S, (p a).w (o a) := Finset.prod_nonneg (by intro a _; exact (p a).nonneg _)
  apply mul_le_mul_of_nonneg_left _ hp
  calc
    _ ≤ ∏ _a ∈ S, δ := by
      apply Finset.prod_le_prod₀
      · intro a _
        exact mul_nonneg (hsurv0 a) hδ0
      · intro a _
        simpa using mul_le_mul_of_nonneg_right (hsurv1 a) hδ0
    _ = _ := by simp

/-- Positive-weight ordinary target matches identify all distinguished arrival labels and times. -/
theorem ordinary_targets_canonical_times {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (S : Finset R) (o : ∀ a, Ω a)
    (hweight : (clockFieldLaw (edgeLaw δ hδ0 hδ1 p lab)).w ξ ≠ 0)
    (hmatch : ∀ a ∈ S, ∃ y, (greedyMatching (overlay ins ξ)).assignment a = some (y, o a) ∧ ins (a, y) = none) :
    ∃ times : S → Fin T,
      (∀ a ∈ S, (greedyMatching (overlay ins ξ)).assignment a = some (lab a (o a), o a) ∧ ins (a, lab a (o a)) = none) ∧
      ∀ a : S, ξ (a.1, lab a.1 (o a.1)) = .tick (times a) (o a.1) := by
  classical
  have hsource (a : S) : ∃ t : Fin T,
      (greedyMatching (overlay ins ξ)).assignment a.1 = some (lab a.1 (o a.1), o a.1) ∧
        ins (a.1, lab a.1 (o a.1)) = none ∧ ξ (a.1, lab a.1 (o a.1)) = .tick t (o a.1) := by
    obtain ⟨y, ha, hins⟩ := hmatch a.1 a.2
    obtain ⟨t, ht⟩ := greedyMatching_assignment_source (overlay ins ξ) a.1 y (o a.1) ha
    have hraw : ξ (a.1, y) = .tick t (o a.1) := by simpa [overlay, hins] using ht
    have hy := arrival_label_of_weight_ne_zero δ hδ0 hδ1 p lab ξ a.1 y t (o a.1) hraw hweight
    subst y
    exact ⟨t, ha, hins, hraw⟩
  choose times htimes using hsource
  refine ⟨times, ?_, ?_⟩
  · intro a ha
    exact ⟨(htimes ⟨a, ha⟩).1, (htimes ⟨a, ha⟩).2.1⟩
  · intro a
    exact (htimes a).2.2

noncomputable def targetSurvivalKernel {T : ℕ} [Nonempty (Fin T)] {R : Type*}
    [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (S : Finset R) (o : ∀ a, Ω a) (times : S → Fin T)
    (bg : ∀ e : {e // e ∈ backgroundEdges S (S.image fun a => lab a (o a))},
      MeshClockValue T (Ω e.1.1)) : ℝ :=
  ∏ e : RowLabel R g, survival δ (labMarg (p e.1) (lab e.1) e.2)
    (targetCrossCutoff ins (fillBackground (backgroundEdges S (S.image fun a => lab a (o a))) bg)
      S o lab (extendTargetTimes S times) e)

/-- Counting ordinary target arrivals and integrating their times preserves the full atom product. -/
theorem ordinary_target_probability_from_survival {T : ℕ} [Nonempty (Fin T)] {R : Type*}
    [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (S : Finset R) (o : ∀ a, Ω a) (hInj : Set.InjOn (fun a => lab a (o a)) S)
    (Good : (∀ e : {e // e ∈ backgroundEdges S (S.image fun a => lab a (o a))},
      MeshClockValue T (Ω e.1.1)) → Prop)
    (C ε : ℝ) (f : Fin T → ℝ) (hC : 0 ≤ C) (hf : ∀ t, 0 ≤ f t)
    (hexception : (FinProb.pi (fun e : {e // e ∈ backgroundEdges S (S.image fun a => lab a (o a))} =>
      edgeLaw δ hδ0 hδ1 p lab e.1)).pr (fun bg => ¬ Good bg) ≤ ε)
    (hgood : ∀ times bg, Good bg → targetSurvivalKernel δ p lab ins S o times bg ≤
      C * ∏ a : S, f (times a))
    (hintegral : δ * ∑ t, f t ≤ 1) :
    (clockFieldLaw (edgeLaw δ hδ0 hδ1 p lab)).pr
      (fun ξ => ∀ a ∈ S, ∃ y, (greedyMatching (overlay ins ξ)).assignment a = some (y, o a) ∧ ins (a, y) = none) ≤
      (∏ a ∈ S, (p a).w (o a)) * (C + ε * (δ * (T : ℝ)) ^ S.card) := by
  classical
  let L := S.image fun a => lab a (o a)
  let D := backgroundEdges S L
  let law := clockFieldLaw (edgeLaw (T := T) δ hδ0 hδ1 p lab)
  let Pbg := FinProb.pi (fun e : {e // e ∈ D} => edgeLaw (T := T) δ hδ0 hδ1 p lab e.1)
  let Φ := targetSurvivalKernel δ p lab ins S o
  let W (times : S → Fin T) := (∏ a ∈ S, (p a).w (o a)) *
    ∏ a ∈ S, survival δ (labMarg (p a) (lab a) (lab a (o a))) (extendTargetTimes S times a).val * δ
  let Rect (times : S → Fin T) (ξ : ClockField T R g Ω) : Prop :=
    (∀ a ∈ S, ξ (a, lab a (o a)) = .tick (extendTargetTimes S times a) (o a)) ∧
      ∀ e, NoEarlyArrival (targetCrossCutoff ins (fillBackground D (fun j => ξ j.1))
        S o lab (extendTargetTimes S times) e) (ξ e)
  have hL : ∀ a ∈ S, lab a (o a) ∈ L := by
    intro a ha
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hD : ∀ a ∈ S, (a, lab a (o a)) ∉ D := by
    intro a ha
    simp [D, backgroundEdges, ha]
  have hfactor (times : S → Fin T) : law.pr (Rect times) = W times * Pbg.expect (Φ times) := by
    let cut (bg : ∀ e : {e // e ∈ D}, MeshClockValue T (Ω e.1.1)) :=
      targetCrossCutoff ins (fillBackground D bg) S o lab (extendTargetTimes S times)
    have hc : ∀ bg e, cut bg e ≤ T := by
      intro bg e
      exact targetCrossCutoff_le ins _ S o lab _ hInj e
    have hzT : ∀ bg a, a ∈ S → cut bg (a, lab a (o a)) = 0 := by
      intro bg a ha
      exact extendCrossCutoff_target_zero S L o lab hL _ a ha
    have hzD : ∀ bg e, e ∈ D → cut bg e = 0 := by
      intro bg e he
      exact extendCrossCutoff_background_zero S L o lab hL _ e he
    exact target_rectangle_background_factorization δ hδ0 hδ1 p lab S o
      (extendTargetTimes S times) D hD cut hc hzT hzD
  have hbase (e : RowLabel R g) : 0 ≤ 1 - δ * labMarg (p e.1) (lab e.1) e.2 :=
    sub_nonneg.mpr (mul_le_one₀ hδ1 (labMarg_nonneg _ _ _) (labMarg_le_one _ _ _))
  have hΦ0 (times : S → Fin T) (bg : ∀ e : {e // e ∈ D}, MeshClockValue T (Ω e.1.1)) :
      0 ≤ Φ times bg := by
    unfold Φ targetSurvivalKernel
    exact Finset.prod_nonneg (by intro e _; exact pow_nonneg (hbase e) _)
  have hΦ1 (times : S → Fin T) (bg : ∀ e : {e // e ∈ D}, MeshClockValue T (Ω e.1.1)) :
      Φ times bg ≤ 1 := survival_product_le_one δ
    (fun e : RowLabel R g => labMarg (p e.1) (lab e.1) e.2)
    (targetCrossCutoff ins (fillBackground D bg) S o lab (extendTargetTimes S times))
    hδ0 hδ1 (fun e => labMarg_nonneg _ _ _) (fun e => labMarg_le_one _ _ _)
  have hExp0 (times : S → Fin T) : 0 ≤ Pbg.expect (Φ times) := by
    unfold FinProb.expect
    exact Finset.sum_nonneg (by intro bg _; exact mul_nonneg (Pbg.nonneg bg) (hΦ0 times bg))
  have hnecessary (ξ : ClockField T R g Ω) (hweight : law.w ξ ≠ 0)
      (hmatch : ∀ a ∈ S, ∃ y, (greedyMatching (overlay ins ξ)).assignment a = some (y, o a) ∧ ins (a, y) = none) :
      ∃ times : S → Fin T, Rect times ξ := by
    obtain ⟨times, hcan, hraw⟩ := ordinary_targets_canonical_times δ hδ0 hδ1 p lab ins ξ S o hweight hmatch
    have hraw' : ∀ a ∈ S, ξ (a, lab a (o a)) = .tick (extendTargetTimes S times a) (o a) := by
      intro a ha
      simpa [extendTargetTimes, ha] using hraw ⟨a, ha⟩
    have hclock : ∀ a ∈ S, overlay ins ξ (a, lab a (o a)) = .tick (extendTargetTimes S times a) (o a) := by
      intro a ha
      simpa [overlay, (hcan a ha).2] using hraw' a ha
    have hsurv := target_matching_cross_survival ins ξ S o lab (extendTargetTimes S times) hInj
      (fun a ha => (hcan a ha).1) hclock
    refine ⟨times, hraw', ?_⟩
    intro e
    rw [← targetCrossCutoff_fillBackground ins ξ S o lab (extendTargetTimes S times)]
    exact hsurv e
  have hUnion : law.pr
      (fun ξ => ∀ a ∈ S, ∃ y, (greedyMatching (overlay ins ξ)).assignment a = some (y, o a) ∧ ins (a, y) = none) ≤
        ∑ times : S → Fin T, law.pr (Rect times) := by
    calc
      _ ≤ law.pr (fun ξ => ∃ times : S → Fin T, Rect times ξ) :=
        pr_le_of_weighted_implication law _ _ hnecessary
      _ ≤ _ := by
        simpa using finProb_pr_biUnion_le_sum law (Finset.univ : Finset (S → Fin T)) Rect
  have hp : 0 ≤ ∏ a ∈ S, (p a).w (o a) := Finset.prod_nonneg (by intro a _; exact (p a).nonneg _)
  have hrect (times : S → Fin T) : law.pr (Rect times) ≤
      ((∏ a ∈ S, (p a).w (o a)) * δ ^ S.card) * Pbg.expect (Φ times) := by
    rw [hfactor]
    exact mul_le_mul_of_nonneg_right
      (arrival_time_factor_le δ hδ0 hδ1 p lab S o (extendTargetTimes S times)) (hExp0 times)
  have hInt : δ ^ S.card * (∑ times : S → Fin T, Pbg.expect (Φ times)) ≤
      C + ε * (δ * (T : ℝ)) ^ S.card := by
    simpa only [Fintype.card_coe] using target_integral_with_exception (I := S) Pbg Good
      δ C ε f Φ hδ0 hC hf hgood hΦ1 hexception hintegral
  calc
    _ ≤ ∑ times : S → Fin T, law.pr (Rect times) := hUnion
    _ ≤ ∑ times : S → Fin T, ((∏ a ∈ S, (p a).w (o a)) * δ ^ S.card) * Pbg.expect (Φ times) := by
      exact Finset.sum_le_sum (by intro times _; exact hrect times)
    _ = (∏ a ∈ S, (p a).w (o a)) * (δ ^ S.card * ∑ times : S → Fin T, Pbg.expect (Φ times)) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hInt hp

end HypercubeRamsey.Lane_sol_clock_s7
