import HypercubeRamsey.S15.DirectNodes
import HypercubeRamsey.S15.Masks
import HypercubeRamsey.S15.Capacity
import HypercubeRamsey.S15.ClusterNodes_q_s15_c1
import HypercubeRamsey.S15.ClusterNodes_q_s15_c3
import HypercubeRamsey.S15.ClusterNodes_sol_s15_mask
import HypercubeRamsey.S15.MaskTransfer_sol_s15_mask
import HypercubeRamsey.S15.ClusterNodes_q_s15_c2
import HypercubeRamsey.S15.ClusterNodes_sol_s15_transfer
import HypercubeRamsey.S15.ClusterNodes_q_s15_c1
import HypercubeRamsey.S15.ClusterNodes_sol_s15_load
import HypercubeRamsey.S15.ClusterNominal_sol_s15_transfer

/-! History alarms, cluster mass, and the conditional bin and label stages of Section 15. -/

namespace HypercubeRamsey.S15

open HypercubeRamsey Filter Classical
open scoped BigOperators

/-- A test of the degree and crossing alarms from L15.2a. -/
noncomputable def clusterCrossingRemovedMass {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k) : ℝ :=
  ∑ x, if clusterJ0 PT hPT hm W a x ∧
      ∃ b ∈ clusterCrossingNeighbours PT hPT a,
        |clusterDegree PT hPT hm W b x - 1 / 2| > 2 * bstar T k then
    (Law.unifCore (PT.tiling.P (patchAt PT hPT a.1)).X
      (hPT.tiling_valid.patch_nonempty (patchAt PT hPT a.1)).1).w x else 0

/-- Raw bounds for the product-of-degrees and crossing-removal tests. -/
def ClusterAlarmTestClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    ∀ a : EvenPosition T k,
      (clusterHistoryLaw PT hPT hm).pr (fun W => clusterAlarm1 PT hPT hm W a) ≤
        Real.exp (-Real.rpow (T.S.n k : ℝ) 0.2) ∧
      ∀ W, clusterCrossingRemovedMass PT hPT hm W a ≤ Real.exp (-(κ.α / 2) * T.S.n k)

/-- Raw mean bound for the large-interaction alarm `T_v(W)`. -/
def ClusterInteractionMeanClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    ∀ a : EvenPosition T k,
      (clusterHistoryLaw PT hPT hm).E (fun W => clusterInteractionCost PT hPT hm W a) ≤
        Real.exp (-300 * PT.tiling.gain (patchAt PT hPT a.1))

/-- Local product-measure comparison after conditioning the histories to avoid the three alarms. -/
structure ClusterHistoryConditioning {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) where
  positive : 0 < (clusterHistoryLaw PT hPT hm).pr (clusterAlarmsAvoided PT hPT hm)
  law : FinLaw (ClusterHistory PT hPT hm)
  law_eq : law = clusterAvoidedHistoryLaw PT hPT hm positive
  avoids : ∀ W, law.w W ≠ 0 → clusterAlarmsAvoided PT hPT hm W
  local_comparison : ∀ F : ClusterHistory PT hPT hm → ℝ,
    (∀ W, 0 ≤ F W) → ∀ U : Finset (ClusterConsultation PT),
      ClusterHistoryDependsOn F (clusterConsultationScope PT hPT hm U) →
      (U.card : ℝ) ≤ (T.S.n k : ℝ) ^ 5 →
        law.E F ≤ (1 + 1 / (T.S.n k : ℝ)) * (clusterHistoryLaw PT hPT hm).E F

/-- The output contract of L15.2c. -/
def ClusterHistoryConditioningClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      Nonempty (ClusterHistoryConditioning PT hPT hm)

/-- L15.2d: the conditional mass tail on positive raw-history support avoiding the alarms. -/
def ClusterMassClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    ∀ W, 0 < (clusterHistoryLaw PT hPT hm).w W →
      clusterAlarmsAvoided PT hPT hm W → ∀ a : EvenPosition T k,
      (clusterInternalKernel PT hPT hm W).pr
        (fun I => clusterRowMass PT hPT hm W I a < 1 / 2) ≤
          (T.S.n k : ℝ) ^ (-(κ.R : ℝ))

/-- L15.2a: the raw alarm-one probability and deterministic crossing-removal bound. -/
theorem high_cluster_degree_alarm (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) : ClusterAlarmTestClaim κ T := by
  sorry

/-- L15.2b: the raw mean large-interaction estimate. -/
theorem high_cluster_interaction_alarm (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) : ClusterInteractionMeanClaim κ T := by
  sorry

/-- L15.2c: product-local-lemma conditioning of the primitive histories. -/
theorem high_cluster_condition_histories (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (hAlarm : ClusterAlarmTestClaim κ T)
    (hInteraction : ClusterInteractionMeanClaim κ T) : ClusterHistoryConditioningClaim κ T := by
  have hAlarm3Probability : ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ a : EvenPosition T k,
        (clusterHistoryLaw PT hPT hm).pr (fun W => clusterAlarm3 PT hPT hm W a) ≤
          Real.exp (-Real.rpow ((PT.tiling.P (patchAt PT hPT a.1)).h : ℝ)
            (1 + κ.c14)) := by
    apply Filter.Eventually.of_forall
    intro k PT hPT hm a
    exact HypercubeRamsey.Lane_q_s15_c1.clusterAlarm3_pr_le_slice_bad PT hPT hm a
  have hAlarm2Probability : ∀ᶠ k in atTop,
      ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ a : EvenPosition T k,
        (clusterHistoryLaw PT hPT hm).pr
          (fun W => clusterAlarm2 PT hPT hm W a) ≤
            Real.exp (-200 * PT.tiling.gain (patchAt PT hPT a.1)) := by
    filter_upwards [hInteraction] with k hk
    intro PT hPT hm a
    exact HypercubeRamsey.Lane_q_s15_c1.clusterAlarm2_pr_le_exp hPT hm a
      (hk PT hPT hm a)
  have hAlarm1Probability : ∀ᶠ k in atTop,
      ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ a : EvenPosition T k,
        (clusterHistoryLaw PT hPT hm).pr
          (fun W => clusterAlarm1 PT hPT hm W a) ≤
            Real.exp (-Real.rpow (T.S.n k : ℝ) 0.2) := by
    filter_upwards [hAlarm] with k hk
    intro PT hPT hm a
    exact (hk PT hPT hm a).1
  have hRowAlarmProbability : ∀ᶠ k in atTop,
      ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ a : EvenPosition T k,
        (clusterHistoryLaw PT hPT hm).pr
          (fun W => HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarm PT hPT hm W a) ≤
            Real.exp (-Real.rpow (T.S.n k : ℝ) 0.2) +
              Real.exp (-200 * PT.tiling.gain (patchAt PT hPT a.1)) +
                Real.exp (-Real.rpow ((PT.tiling.P (patchAt PT hPT a.1)).h : ℝ)
                  (1 + κ.c14)) := by
    filter_upwards [hAlarm1Probability, hAlarm2Probability, hAlarm3Probability]
      with k hk1 hk2 hk3
    intro PT hPT hm a
    calc
      (clusterHistoryLaw PT hPT hm).pr
          (fun W => HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarm PT hPT hm W a) ≤
          (clusterHistoryLaw PT hPT hm).pr (fun W => clusterAlarm1 PT hPT hm W a) +
            (clusterHistoryLaw PT hPT hm).pr (fun W => clusterAlarm2 PT hPT hm W a) +
              (clusterHistoryLaw PT hPT hm).pr (fun W => clusterAlarm3 PT hPT hm W a) := by
        exact HypercubeRamsey.Lane_q_s15_c1.finLaw_pr_or3_le_add
          (clusterHistoryLaw PT hPT hm)
          (fun W => clusterAlarm1 PT hPT hm W a)
          (fun W => clusterAlarm2 PT hPT hm W a)
          (fun W => clusterAlarm3 PT hPT hm W a)
      _ ≤ Real.exp (-Real.rpow (T.S.n k : ℝ) 0.2) +
            Real.exp (-200 * PT.tiling.gain (patchAt PT hPT a.1)) +
              Real.exp (-Real.rpow ((PT.tiling.P (patchAt PT hPT a.1)).h : ℝ)
                (1 + κ.c14)) := by
        exact add_le_add (add_le_add (hk1 PT hPT hm a) (hk2 PT hPT hm a))
          (hk3 PT hPT hm a)
  have hnEventually : ∀ᶠ k in atTop, 2 ≤ T.S.n k :=
    T.S.n_tendsto.eventually_ge_atTop 2
  have hnReal : Filter.Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hlogT : Filter.Tendsto (fun k => Real.log (T.S.n k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hnReal
  have hThresholdEventually : ∀ᶠ k in atTop,
      10 ^ 7 / κ.a ≤ Real.log (T.S.n k : ℝ) := by
    have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
    exact hlogT.eventually_ge_atTop (10 ^ 7 / κ.a)
  have hRadiusEventually :=
    HypercubeRamsey.Lane_q_s15_c1.clusterPatch_radius_eventually κ hκ T
  filter_upwards [hRowAlarmProbability, hnEventually, hThresholdEventually, hRadiusEventually]
    with k hkProb hkN hkThreshold hkRadius
  intro PT hPT hm
  let L := Real.log (T.S.n k : ℝ)
  let x : EvenPosition T k → ℝ := fun a =>
    HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarmCharge PT hPT hm a
  let p : EvenPosition T k → ℝ := fun a => x a / 2
  have hrawHalf : ∀ a, (clusterHistoryLaw PT hPT hm).pr
      (HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarm PT hPT hm · a) ≤ p a := by
    intro a
    have hFacts := HypercubeRamsey.Lane_q_s15_c1.clusterHighRow_charge_facts
      PT hPT hm hκ a hkN L rfl hkThreshold
      (hkRadius PT hPT hm (patchAt PT hPT a.1))
    have hraw := hkProb PT hPT hm a
    have hhalf := HypercubeRamsey.Lane_q_s15_c1.clusterBadProbability_pr_le_half_charge
      (HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarm PT hPT hm · a)
      (clusterHistoryLaw PT hPT hm) (T.S.n k : ℝ)
      (PT.tiling.gain (patchAt PT hPT a.1))
      ((PT.tiling.P (patchAt PT hPT a.1)).h : ℝ) κ.c14
      (le_trans (by norm_num) hFacts.1) hFacts.2.1 hFacts.2.2.1 hFacts.2.2.2.1 hraw
    simpa [p, x, HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarmCharge] using hhalf
  have hx0 : ∀ a, 0 ≤ x a := by
    intro a
    unfold x HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarmCharge
    exact (Real.exp_pos _).le
  have hx1 : ∀ a, x a < 1 := by
    intro a
    have hFacts := HypercubeRamsey.Lane_q_s15_c1.clusterHighRow_charge_facts
      PT hPT hm hκ a hkN L rfl hkThreshold
      (hkRadius PT hPT hm (patchAt PT hPT a.1))
    unfold x HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarmCharge
    rw [← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    nlinarith [hFacts.1]
  have hpx : ∀ a, p a ≤ x a * ∏ a' ∈ Finset.univ.filter
      (HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarmAdjacent PT hPT hm a),
        (1 - x a') := by
    classical
    intro a
    let Nbrs := Finset.univ.filter
      (HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarmAdjacent PT hPT hm a)
    let Overlap := Finset.univ.filter fun a' : EvenPosition T k =>
      ∃ r : HypercubeRamsey.S15.ClusterRecordIndex PT hPT hm,
        r ∈ HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarmVariables PT hPT hm a ∧
        r ∈ HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarmVariables PT hPT hm a'
    have hsub : Nbrs ⊆ Overlap := by
      intro a' ha'
      rcases Finset.mem_filter.mp ha' with ⟨_, hadj⟩
      have hshared : ∃ r, r ∈
          HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarmVariables PT hPT hm a ∧ r ∈
          HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarmVariables PT hPT hm a' := by
        by_contra hnone
        apply hadj.2
        apply Finset.disjoint_left.mpr
        intro r hr hr'
        exact hnone ⟨r, hr, hr'⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hshared⟩
    have hchargeEq : ∀ a' ∈ Nbrs, x a' = x a := by
      intro a' ha'
      rcases (Finset.mem_filter.mp ha').2 with ⟨hne, hnoverlap⟩
      have hshared : ∃ r, r ∈
          HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarmVariables PT hPT hm a ∧ r ∈
          HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarmVariables PT hPT hm a' := by
        by_contra hnone
        exact hnoverlap (Finset.disjoint_left.mpr (by
          intro r hr hr'
          exact hnone ⟨r, hr, hr'⟩))
      rcases hshared with ⟨r, hr, hr'⟩
      have hrows := HypercubeRamsey.Lane_q_s15_c1.clusterRowConsultationScopes_intersection_geometry
        PT hPT hm a a' r hr hr'
      rcases hrows with ⟨i, hi, hi', _, _⟩
      have hpatch : patchAt PT hPT a.1 = patchAt PT hPT a'.1 := hi.trans hi'.symm
      unfold x HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarmCharge
      rw [hpatch]
    have hsumX : (∑ a' ∈ Nbrs, x a') ≤ 1 / 2 := by
      calc
        _ = ∑ a' ∈ Nbrs, x a := by
          apply Finset.sum_congr rfl
          intro a' ha'
          rw [hchargeEq a' ha']
        _ = (Nbrs.card : ℝ) * x a := by simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (Overlap.card : ℝ) * x a := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub)
            (hx0 a)
        _ ≤ 1 / 2 := by
          have hFacts := HypercubeRamsey.Lane_q_s15_c1.clusterHighRow_charge_facts
            PT hPT hm hκ a hkN L rfl hkThreshold
            (hkRadius PT hPT hm (patchAt PT hPT a.1))
          have hOverlapBound := hFacts.2.2.2.2
          change (Overlap.card : ℝ) * x a ≤ 1 / 2 at hOverlapBound
          exact hOverlapBound
    have hProdLower := HypercubeRamsey.Lane_q_s15_c1.clusterProd_one_sub_lower Nbrs x
      (fun a' ha' => hx0 a') (fun a' ha' => (hx1 a').le)
    have hProdHalf : (1 / 2 : ℝ) ≤ ∏ a' ∈ Nbrs, (1 - x a') := by
      calc
        (1 / 2 : ℝ) ≤ 1 - ∑ a' ∈ Nbrs, x a' := by linarith [hsumX]
        _ ≤ ∏ a' ∈ Nbrs, (1 - x a') := hProdLower
    change x a / 2 ≤ x a * ∏ a' ∈ Nbrs, (1 - x a')
    calc
      x a / 2 = x a * (1 / 2) := by ring
      _ ≤ x a * ∏ a' ∈ Nbrs, (1 - x a') :=
        mul_le_mul_of_nonneg_left hProdHalf (hx0 a)
  let E := HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarmEventSet PT hPT hm
  let w := HypercubeRamsey.Lane_q_s15_c1.clusterHistoryProductWeight PT hPT hm
  let adj := HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarmAdjacent PT hPT hm
  letI : DecidableRel adj := Classical.decRel _
  have hsymm : ∀ a a', adj a a' → adj a' a := by
    intro a a' hadj
    refine ⟨hadj.1.symm, ?_⟩
    intro hdis
    apply hadj.2
    exact Finset.disjoint_left.mpr (by
      intro r hr hr'
      exact (Finset.disjoint_left.mp hdis) hr' hr)
  have hirr : ∀ a, ¬ adj a a := by
    intro a hadj
    exact hadj.1 rfl
  have hLocalLemma := LocalLemma.conditional_avoidance w
    (HypercubeRamsey.Lane_q_s15_c1.clusterHistoryProductWeight_nonneg PT hPT hm)
    (HypercubeRamsey.Lane_q_s15_c1.clusterHistoryProductWeight_sum_one PT hPT hm)
    E adj hsymm hirr p x
    (HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarm_LLL_independent_bound_of_raw
      PT hPT hm p hrawHalf)
    hx0 hx1 hpx
  have hAvoid : ∀ W, W ∈ LocalLemma.avoid E Finset.univ ↔
      clusterAlarmsAvoided PT hPT hm W := by
    intro W
    have hE : ∀ a, W ∈ E a ↔
        HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarm PT hPT hm W a := by
      intro a
      simp [E, HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarmEventSet]
    have hAvoidEvent : W ∈ LocalLemma.avoid E Finset.univ ↔
        ∀ a, ¬ HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarm PT hPT hm W a := by
      unfold LocalLemma.avoid
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h a hb
        exact h a True.intro ((hE a).mpr hb)
      · intro h a ha hb
        exact h a ((hE a).mp hb)
    have hPred : (∀ a, ¬ HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarm
          PT hPT hm W a) ↔ clusterAlarmsAvoided PT hPT hm W := by
      simp [clusterAlarmsAvoided, HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarm]
    exact hAvoidEvent.trans hPred
  have hPositive : 0 < (clusterHistoryLaw PT hPT hm).pr
      (clusterAlarmsAvoided PT hPT hm) := by
    calc
      0 < LocalLemma.mass w (LocalLemma.avoid E Finset.univ) := hLocalLemma.1
      _ = (clusterHistoryLaw PT hPT hm).pr
          (fun W => W ∈ LocalLemma.avoid E Finset.univ) :=
        HypercubeRamsey.Lane_q_s15_c1.clusterHistoryProductWeight_mass_eq_pr
          PT hPT hm (LocalLemma.avoid E Finset.univ)
      _ = (clusterHistoryLaw PT hPT hm).pr (clusterAlarmsAvoided PT hPT hm) := by
        congr 1
        funext W
        exact propext (hAvoid W)
  let law := clusterAvoidedHistoryLaw PT hPT hm hPositive
  refine ⟨hPositive, law, rfl, ?_, ?_⟩
  · intro W hW
    by_contra havoid
    have hzero : law.w W = 0 := by
      simp [law, clusterAvoidedHistoryLaw, FinLaw.cond, havoid]
    exact hW hzero
  · intro F hF U hdepends hUcard
    classical
    let Touched := Finset.univ.filter fun a : EvenPosition T k =>
      ∃ r : HypercubeRamsey.S15.ClusterRecordIndex PT hPT hm,
        r ∈ clusterConsultationScope PT hPT hm U ∧
        r ∈ clusterConsultationScope PT hPT hm
          (HypercubeRamsey.Lane_q_s15_c1.clusterRowConsultations PT hPT hm a)
    let Far := Finset.univ \ Touched
    have hST : Disjoint Far Touched := by
      apply Finset.disjoint_left.mpr
      intro a haFar haTouch
      exact (Finset.mem_sdiff.mp haFar).2 haTouch
    have hUnion : Far ∪ Touched = Finset.univ := by
      ext a
      simp [Far]
    have hScopeDisj : Disjoint (clusterConsultationScope PT hPT hm U)
        (Far.biUnion (HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarmVariables PT hPT hm)) := by
      apply Finset.disjoint_left.mpr
      intro r hrU hrFar
      rcases Finset.mem_biUnion.mp hrFar with ⟨a, haFar, hrA⟩
      have hnotTouch : a ∉ Touched := (Finset.mem_sdiff.mp haFar).2
      have htouch : a ∈ Touched := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        exact ⟨r, hrU, hrA⟩
      exact (hnotTouch htouch).elim
    have hRadiusU : ∀ c ∈ U,
        8 ≤ 10 * κ.ρ * (PT.tiling.P c.1.1).h := by
      intro c hc
      exact hkRadius PT hPT hm c.1.1
    have hTouchedSum : (∑ a ∈ Touched, x a) ≤ Real.exp (-L) / 2 := by
      have h := HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarmTouching_charge_sum_bound
        PT hPT hm hκ U hkN L rfl hkThreshold hRadiusU hUcard
      simpa [Touched, x, HypercubeRamsey.Lane_q_s15_c1.clusterRowAlarmCharge] using h
    have hnPositive : (0 : ℝ) < (T.S.n k : ℝ) := by
      exact_mod_cast (show 0 < T.S.n k by omega)
    have hnExp : (T.S.n k : ℝ) = Real.exp L := by
      dsimp [L]
      exact (Real.exp_log hnPositive).symm
    have hExpNeg : Real.exp (-L) = 1 / (T.S.n k : ℝ) := by
      rw [Real.exp_neg, hnExp]
      ring
    have hProdLower : 1 - ∑ a ∈ Touched, x a ≤
        ∏ a ∈ Touched, (1 - x a) :=
      HypercubeRamsey.Lane_q_s15_c1.clusterProd_one_sub_lower Touched x
        (fun a ha => hx0 a) (fun a ha => (hx1 a).le)
    let q := ∏ a ∈ Touched, (1 - x a)
    have hqPos : 0 < q := by
      apply Finset.prod_pos
      intro a ha
      exact sub_pos.mpr (hx1 a)
    have hqLower : (1 + 1 / (T.S.n k : ℝ))⁻¹ ≤ q := by
      have hsimple : (1 + 1 / (T.S.n k : ℝ))⁻¹ ≤
          1 - 1 / (2 * (T.S.n k : ℝ)) := by
        have hn1 : (1 : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast (by omega : 1 ≤ T.S.n k)
        have hC : 0 < 1 + 1 / (T.S.n k : ℝ) := by positivity
        field_simp [ne_of_gt hnPositive, ne_of_gt hC]
        nlinarith [hn1]
      calc
        _ ≤ 1 - Real.exp (-L) / 2 := by
          rw [hExpNeg]
          calc
            _ ≤ 1 - 1 / (2 * (T.S.n k : ℝ)) := hsimple
            _ = 1 - 1 / (T.S.n k : ℝ) / 2 := by ring
        _ ≤ 1 - ∑ a ∈ Touched, x a := sub_le_sub_left hTouchedSum 1
        _ ≤ q := hProdLower
    have hqInv : q⁻¹ ≤ 1 + 1 / (T.S.n k : ℝ) := by
      have hC : 0 < 1 + 1 / (T.S.n k : ℝ) := by positivity
      have hmul : 1 ≤ q * (1 + 1 / (T.S.n k : ℝ)) := by
        calc
          1 = (1 + 1 / (T.S.n k : ℝ))⁻¹ *
              (1 + 1 / (T.S.n k : ℝ)) :=
                (inv_mul_cancel₀ (ne_of_gt hC)).symm
          _ ≤ q * (1 + 1 / (T.S.n k : ℝ)) :=
            mul_le_mul_of_nonneg_right hqLower hC.le
      rw [inv_eq_one_div]
      apply (div_le_iff₀ hqPos).2
      simpa [mul_comm] using hmul
    have hAvoidPos : ∀ S : Finset (EvenPosition T k),
        0 < LocalLemma.mass w (LocalLemma.avoid E S) := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
          have hsum : ∑ W, w W = 1 := by
            simpa [w] using
              HypercubeRamsey.Lane_q_s15_c1.clusterHistoryProductWeight_sum_one PT hPT hm
          have hmass : LocalLemma.mass w (LocalLemma.avoid E ∅) = ∑ W, w W := by
            simp [LocalLemma.mass, LocalLemma.avoid]
          rw [hmass, hsum]
          norm_num
      | @insert a S ha ih =>
          have havoidInsert : LocalLemma.avoid E (insert a S) =
              LocalLemma.avoid E S \ E a := by
            ext W
            simp only [LocalLemma.avoid, Finset.mem_filter, Finset.mem_univ,
              true_and, Finset.mem_sdiff]
            change (∀ j ∈ insert a S, W ∉ E j) ↔
              ((∀ j ∈ S, W ∉ E j) ∧ W ∉ E a)
            constructor
            · intro h
              exact ⟨fun j hj => h j (Finset.mem_insert_of_mem hj),
                h a (Finset.mem_insert_self a S)⟩
            · rintro ⟨hS, ha⟩ j hj
              rcases Finset.mem_insert.mp hj with rfl | hj
              · exact ha
              · exact hS j hj
          have hsplit : LocalLemma.mass w (LocalLemma.avoid E (insert a S)) +
              LocalLemma.mass w (E a ∩ LocalLemma.avoid E S) =
                LocalLemma.mass w (LocalLemma.avoid E S) := by
            rw [havoidInsert]
            have hs := Finset.sum_inter_add_sum_sdiff
              (LocalLemma.avoid E S) (E a) w
            unfold LocalLemma.mass
            rw [Finset.inter_comm (E a) (LocalLemma.avoid E S)]
            exact (add_comm _ _).trans hs
          have hbound := hLocalLemma.2.1 a S ha
          have hlower : (1 - x a) * LocalLemma.mass w (LocalLemma.avoid E S) ≤
              LocalLemma.mass w (LocalLemma.avoid E (insert a S)) := by
            rw [← hsplit]
            have hbound' : LocalLemma.mass w (E a ∩ LocalLemma.avoid E S) ≤
                x a * (LocalLemma.mass w (LocalLemma.avoid E (insert a S)) +
                  LocalLemma.mass w (E a ∩ LocalLemma.avoid E S)) := by
              rw [← hsplit] at hbound
              exact hbound
            nlinarith [hbound']
          exact lt_of_lt_of_le (mul_pos (sub_pos.mpr (hx1 a)) ih) hlower
    have hnumFactor := HypercubeRamsey.Lane_q_s15_c1.clusterHistory_sum_mul_avoid_disjoint_scope
      PT hPT hm F U Far hdepends hScopeDisj
    have hratioFar :
        (∑ W ∈ LocalLemma.avoid E Far, w W * F W) /
          LocalLemma.mass w (LocalLemma.avoid E Far) =
            (clusterHistoryLaw PT hPT hm).E F := by
      have hpos := hAvoidPos Far
      rw [show (∑ W ∈ LocalLemma.avoid E Far, w W * F W) =
          (clusterHistoryLaw PT hPT hm).E F *
            LocalLemma.mass w (LocalLemma.avoid E Far) by
          simpa [w] using hnumFactor]
      exact mul_div_cancel_right₀ _ (ne_of_gt hpos)
    have hcomp := hLocalLemma.2.2.1 Far Touched hST F hF
    rw [hUnion] at hcomp
    let A := Finset.univ.filter (fun W : ClusterHistory PT hPT hm =>
      clusterAlarmsAvoided PT hPT hm W)
    have hAset : A = LocalLemma.avoid E Finset.univ := by
      ext W
      simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using
        (hAvoid W).symm
    have hApos : 0 < ∑ z ∈ A, (clusterHistoryLaw PT hPT hm).w z := by
      have hmass : LocalLemma.mass w (LocalLemma.avoid E Finset.univ) =
          ∑ z ∈ A, (clusterHistoryLaw PT hPT hm).w z := by
        unfold LocalLemma.mass
        calc
          _ = ∑ z ∈ LocalLemma.avoid E Finset.univ,
              (clusterHistoryLaw PT hPT hm).w z := by
            apply Finset.sum_congr rfl
            intro z hz
            have hw := HypercubeRamsey.Lane_q_s15_c1.clusterHistoryLaw_weight_eq_product
              PT hPT hm z
            simpa [w] using hw.symm
          _ = _ := by rw [← hAset]
      calc
        0 < LocalLemma.mass w (LocalLemma.avoid E Finset.univ) := hLocalLemma.1
        _ = _ := hmass
    have cond_E (P : FinLaw (ClusterHistory PT hPT hm))
        (B : Finset (ClusterHistory PT hPT hm))
        (hB : 0 < ∑ z ∈ B, P.w z)
        (G : ClusterHistory PT hPT hm → ℝ) :
        (FinLaw.cond P B hB).E G =
          (∑ z ∈ B, P.w z * G z) / (∑ z ∈ B, P.w z) := by
      classical
      unfold FinLaw.E FinLaw.cond
      calc
        _ = (∑ z, (if z ∈ B then P.w z else 0) * G z) /
            (∑ z ∈ B, P.w z) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro z hz
          ring_nf
        _ = (∑ z ∈ B, P.w z * G z) / (∑ z ∈ B, P.w z) := by
          apply congrArg (fun t : ℝ => t / (∑ z ∈ B, P.w z))
          simp only [ite_mul, zero_mul, Finset.sum_ite_mem_eq]
    have hLawRatio : law.E F =
        (∑ W ∈ LocalLemma.avoid E Finset.univ, w W * F W) /
          LocalLemma.mass w (LocalLemma.avoid E Finset.univ) := by
      change (FinLaw.cond (clusterHistoryLaw PT hPT hm) A hApos).E F = _
      rw [cond_E]
      rw [hAset]
      congr 1
    calc
      law.E F =
          (∑ W ∈ LocalLemma.avoid E Finset.univ, w W * F W) /
            LocalLemma.mass w (LocalLemma.avoid E Finset.univ) := hLawRatio
      _ ≤ q⁻¹ * ((∑ W ∈ LocalLemma.avoid E Far, w W * F W) /
          LocalLemma.mass w (LocalLemma.avoid E Far)) := by
        simpa [w, q] using hcomp
      _ = q⁻¹ * (clusterHistoryLaw PT hPT hm).E F := by rw [hratioFar]
      _ ≤ (1 + 1 / (T.S.n k : ℝ)) * (clusterHistoryLaw PT hPT hm).E F :=
        mul_le_mul_of_nonneg_right hqInv (by
          unfold FinLaw.E
          apply Finset.sum_nonneg
          intro W _
          exact mul_nonneg ((clusterHistoryLaw PT hPT hm).nonneg W) (hF W))

/-- L15.2d: the conditional row mass estimate from the crossing filter and three alarm bounds. -/
theorem high_cluster_conditional_mass_estimate (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (hCross : ClusterCrossingClaim κ T)
    (hAlarm : ClusterAlarmTestClaim κ T) (hInteraction : ClusterInteractionMeanClaim κ T)
    (hConditioning : ClusterHistoryConditioningClaim κ T) : ClusterMassClaim κ T := by
  filter_upwards [hAlarm] with k hkAlarm
  intro PT hPT hm W hW hAvoid a
  have hZero := Lane_sol_s15_load.clusterSigma_zero_probability PT hPT hm W hAvoid a
  have hRemoval : ∀ I : ClusterInternalData PT,
      (∑ x, if clusterJ PT hPT hm W a x then 0 else clusterSigma PT hPT hm W I a x) ≤
      ((PT.tiling.P (patchAt PT hPT a.1)).M *
        ((2 : ℝ) ^ (PT.tiling.P (patchAt PT hPT a.1)).h *
          Real.exp (-500 * PT.tiling.gain (patchAt PT hPT a.1)) / T.S.N k)) *
      (Real.exp (-Real.rpow (T.S.n k : ℝ) 0.2) + Real.exp (-(κ.α / 2) * T.S.n k)) := by
    intro I
    exact Lane_sol_s15_load.clusterSigma_removed_mass_le PT hPT hm W hW hAvoid I a _
      ((hkAlarm PT hPT hm a).2 W)
  have hInteractionBudget : clusterInteractionCost PT hPT hm W a ≤
      Real.exp (-100 * PT.tiling.gain (patchAt PT hPT a.1)) := le_of_not_gt (hAvoid a).2.1
  -- Remaining: project the external neighbour labels to independent slice marginals,
  -- apply the crossing chain to the normalized J-restricted row, then average the
  -- heterogeneous bulk moment and its alarm-two envelope over the center experiment.
  sorry

/-- L15.2 (`lem:high-cluster-mass`, 15:91–112): conditional row-mass failure is at most `n^-R`. -/
theorem high_cluster_mass (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) : ClusterMassClaim κ T := by
  have hCrossing := high_direct_crossing_filters κ hκ T hDeep
  have hAlarm := high_cluster_degree_alarm κ hκ T hDeep
  have hInteraction := high_cluster_interaction_alarm κ hκ T hDeep
  have hConditioning := high_cluster_condition_histories κ hκ T hDeep hAlarm hInteraction
  exact high_cluster_conditional_mass_estimate κ hκ T hDeep hCrossing.2
    hAlarm hInteraction hConditioning

/-- P15.3a: the global high-cluster history-load event has probability at least `0.99`. -/
def ClusterHistoryLoadClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    ∀ H : ClusterHistoryConditioning PT hPT hm,
      (99 / 100 : ℝ) ≤ H.law.pr (fun W => clusterHistoryLoad PT hPT hm W)

/-- P15.3a: use scattered moments and history-local comparison to prove global load success. -/
theorem high_cluster_history_load (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04)
    (hConditioning : ClusterHistoryConditioningClaim κ T) : ClusterHistoryLoadClaim κ T := by
  have hsmall := Lane_sol_s15_load.history_load_small_eventually κ hκ T
  have hHost := T.S.eventually_large 1 7
  have hRatio := T.S.ratio_tendsto.eventually_ge_atTop (800 * 384 / κ.θstar)
  have hNsmall : ∀ᶠ k in atTop,
      (T.S.n k : ℝ) ^ 2 / (2 : ℝ) ^ (T.S.n k) < 1 :=
    T.S.n_tendsto.eventually Lane_q_s15_direct.eventually_nat_sq_over_two_pow_lt_one
  filter_upwards [hsmall, hHost, hRatio, hNsmall] with k hsmall hHost hRatio hNsmall
  intro PT hPT hm H
  have htheta : 0 < κ.θstar := hκ.bucket.2.2.2.2
  have hNpos : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
  have hpow : (0 : ℝ) < 2 ^ (T.S.n k) := by positivity
  have hratio : 800 * 384 * (2 : ℝ) ^ (T.S.n k) / T.S.N k ≤ κ.θstar := by
    have h := (div_le_div_iff₀ htheta hpow).mp hRatio
    exact (div_le_iff₀ hNpos).2 (by nlinarith [h])
  have hNupper : (T.S.N k : ℝ) ≤ (T.S.n k : ℝ) * (2 : ℝ) ^ (T.S.n k) := by
    exact_mod_cast hHost.2.2
  have hn2 : (T.S.n k : ℝ) ^ 2 ≤ (2 : ℝ) ^ (T.S.n k) := by
    simpa using ((div_lt_iff₀ hpow).mp hNsmall).le
  have hNbound : (T.S.N k : ℝ) ^ 2 ≤ (8 : ℝ) ^ (T.S.n k) := by
    calc
      _ ≤ ((T.S.n k : ℝ) * (2 : ℝ) ^ (T.S.n k)) ^ 2 := by gcongr
      _ = (T.S.n k : ℝ) ^ 2 * (4 : ℝ) ^ (T.S.n k) := by
        rw [mul_pow]
        congr 1
        rw [pow_two, ← mul_pow]
        norm_num
      _ ≤ (2 : ℝ) ^ (T.S.n k) * (4 : ℝ) ^ (T.S.n k) := by gcongr
      _ = (8 : ℝ) ^ (T.S.n k) := by rw [← mul_pow]; norm_num
  have htail : (1 / 2 : ℝ) ^ (T.S.n k) ≤ 1 / 100 := by
    have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) hHost.1
    norm_num at h
    linarith
  exact Lane_sol_s15_load.historyLoad_probability hκ PT hPT hm H.law
    H.local_comparison hsmall.1 (hsmall.2 PT hPT hm) hratio hNbound htail

/-- P15.3b: actual certificate charges, with a constant supplied by the estimate. -/
def ClusterCapacityClaim (κ : CConsts) (T : Stage) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
    ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    ∀ W, clusterHistoryLoad PT hPT hm W →
      (∀ i (D : Bin PT.tiling i) g, 0 < clusterBinProbability PT hPT hm W g D.1 →
        clusterPinnedCapacityCharge PT hPT hm W D.1 g ≤
          Real.exp (-c * (D.1.card : ℝ) ^ (0.4 : ℝ))) ∧
      (∀ B, (clusterIndependentBinKernel PT hPT hm W).w B ≠ 0 →
        clusterCapacityAvoided PT hPT hm W B →
          ∀ y, clusterGivenBinColumn PT hPT hm W B y ≤ κ.θ0)

/-- P15.3b: capacity certificates bound bin-wise label-column overloads. -/
theorem high_cluster_capacity_certificates (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04)
    (hConditioning : ClusterHistoryConditioningClaim κ T) : ClusterCapacityClaim κ T := by
  sorry

/-- The output contract of the conditioned bin stage in P15.3(i). -/
def ClusterBinStageClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      Nonempty (ClusterBinStage PT hPT hm)

/-- P15.3(ii): the conditional label stage yields an injective assignment with all row mass gates. -/
def ClusterSampleClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      Nonempty (ClusterSample PT hPT hm)

/-- P15.3(i): construct the bin sampler from the conditional mass, load, and capacity tests. -/
theorem high_cluster_bin_stage (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (hMass : ClusterMassClaim κ T)
    (hConditioning : ClusterHistoryConditioningClaim κ T)
    (hHistoryLoad : ClusterHistoryLoadClaim κ T) (hCapacity : ClusterCapacityClaim κ T) :
    ClusterBinStageClaim κ T := by
  sorry

/-- P15.3(ii): conditionally sample the labels and enforce all even-row mass gates. -/
theorem high_cluster_label_stage (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (hMass : ClusterMassClaim κ T)
    (hBins : ClusterBinStageClaim κ T) : ClusterSampleClaim κ T := by
  sorry

/-- P15.3 (`prop:high-cluster-sampling`, 15:119–156): assemble the history, bin, and label stages. -/
theorem high_cluster_sampling (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) : ClusterSampleClaim κ T := by
  have hAlarm := high_cluster_degree_alarm κ hκ T hDeep
  have hInteraction := high_cluster_interaction_alarm κ hκ T hDeep
  have hConditioning := high_cluster_condition_histories κ hκ T hDeep hAlarm hInteraction
  have hMass := high_cluster_mass κ hκ T hDeep
  have hHistoryLoad := high_cluster_history_load κ hκ T hDeep hConditioning
  have hCapacity := high_cluster_capacity_certificates κ hκ T hDeep hConditioning
  have hBins := high_cluster_bin_stage κ hκ T hDeep hMass hConditioning hHistoryLoad hCapacity
  exact high_cluster_label_stage κ hκ T hDeep hMass hBins

/-- The normalized patch column statistic in the final cluster sampler. -/
noncomputable def clusterColumnAverage {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (CS : ClusterSample PT hPT hm) (i : Fin PT.tiling.m)
    (x : Fin (T.S.N k)) (ω : CS.Outcome) : ℝ :=
  let Eᵢ := evenPatchPositions PT.tiling i
  (Eᵢ.card : ℝ)⁻¹ *
    ∑ a ∈ Eᵢ, (PT.tiling.P i).M * CS.row ω a x

/-- The cluster column moment with the prerequisite history-load indicator retained. -/
noncomputable def clusterColumnMoment {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (CS : ClusterSample PT hPT hm) (i : Fin PT.tiling.m)
    (x : Fin (T.S.N k)) : ℝ :=
  CS.law.E (fun ω =>
    if CS.historyLoad ω then clusterColumnAverage CS i x ω ^ (T.S.n k) else 0)

/-- P15.4a: both equation (15.20) bounds, and the individual nominal factor cap. -/
def ClusterRowCapClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    ∀ CS : ClusterSample PT hPT hm,
      (∀ ω a x, CS.row ω a x = clusterRowWeight PT hPT hm (CS.history ω) (CS.internal ω) a x) ∧
      (∀ ω, CS.law.w ω ≠ 0 → CS.historyLoad ω → ∀ a x,
        (PT.tiling.P (patchAt PT hPT a.1)).M * CS.row ω a x ≤
          2 ^ (T.S.n k) * Real.exp (-200 * PT.tiling.gain (patchAt PT hPT a.1))) ∧
      (∀ ω, CS.law.w ω ≠ 0 → CS.historyLoad ω → ∀ a x,
        CS.row ω a x ≤ 4 * clusterSigma PT hPT hm (CS.history ω) (CS.internal ω) a x *
          ∏ b ∈ clusterBulkNeighbours PT hPT a ∪ clusterCrossingNeighbours PT hPT a,
            normalizedHit (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT b.1)) x (CS.label ω b)) ∧
      (∀ i x, x ∈ PT.envelope i → ∀ (b : OddPosition T k) y,
        normalizedHit (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT b.1)) x y ≤ 3)

/-- P15.4b: core fractions, forest/rank tails and the actual crossing-factor deletion cost. -/
def ClusterGeometryClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      (∀ i a, a ∈ evenPatchPositions PT.tiling i →
        ((evenPatchPositions PT.tiling i).filter fun b => clusterCoreNear PT hPT i a b).card ≤
          (evenPatchPositions PT.tiling i).card *
            Real.exp (0.01 * PT.tiling.gain i) / 2 ^ (T.S.n k)) ∧
      (∀ i G j, j ≤ T.S.n k →
        clusterCrossingRankTail PT i G j ≤
          ((T.S.n k : ℝ) ^ 2 * clusterCrossingFraction T k) ^ j) ∧
      (∀ vs G, (clusterCrossingNonisolated PT vs G).card ≤ 2 * clusterCrossingRank PT vs G) ∧
      (∀ i x, x ∈ PT.envelope i → ∀ M : ClusterMask PT, ClusterMaskGeometry PT hPT i M →
        ∀ ys : OddAssignment T k,
        (∏ r ∈ clusterKeptRows M,
          ∏ b ∈ clusterCrossingNeighbours PT hPT (M.positions r),
            normalizedHit (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT b.1)) x (ys b)) ≤
          3 ^ (2 * clusterCrossingRank PT M.positions M.geometric * (PT.tiling.P i).ℓ) *
            ∏ q ∈ clusterAllowedCrossings PT hPT M,
              normalizedHit (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT q.2.1)) x (ys q.2))

/-- P15.4c: the small-bin core-repeat probability pays the cap, with gain to spare. -/
def ClusterSmallBinSpliceClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    PT.tiling.mode = .highSmall → ∀ i,
      clusterCoreRepeatCost PT i ≤
        (2 : ℝ) ^ (-(T.S.n k : ℤ)) * Real.exp (0.01 * PT.tiling.gain i)

/-- P15.4d: conditional comparison for the fixed nonnegative masked row product.
The load and mask indicators remain in the integral after label comparison. -/
def ClusterLabelTransfer (κ : CConsts) (T : Stage) : Prop :=
  ∃ L : ℝ, 0 < L ∧ ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    ∀ CS : ClusterSample PT hPT hm, ∀ i x, x ∈ PT.envelope i →
    ∀ M : ClusterMask PT, ClusterMaskGeometry PT hPT i M →
      clusterMaskedIntegral CS i x M ≤ L ^ (T.S.n k) * clusterAfterLabelIntegral CS i x M

/-- P15.4e: bin comparison followed by reverse integration of the necessary earlier repeats.
Only after bin comparison is the global load restriction discarded. -/
def ClusterBinTransfer (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    ∀ CS : ClusterSample PT hPT hm, ∀ i x, x ∈ PT.envelope i →
    ∀ M : ClusterMask PT, ClusterMaskGeometry PT hPT i M →
      clusterAfterLabelIntegral CS i x M ≤
        2 * clusterCoreRepeatCost PT i ^ M.coreBins.card *
          clusterCrossingFraction T k ^ M.crossingBins.card *
            CS.binStage.historyLaw.E (clusterReferenceMean PT hPT hm i x M)

/-- P15.4f: restore raw histories and factor the kept reference product.
The equality exposes where every remaining nominal external hit integrates to one. -/
def ClusterHistoryRestore (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    ∀ CS : ClusterSample PT hPT hm, ∀ i x, x ∈ PT.envelope i →
    ∀ M : ClusterMask PT, ClusterMaskGeometry PT hPT i M →
      (clusterHistoryLaw PT hPT hm).E (clusterReferenceMean PT hPT hm i x M) =
        ∏ r ∈ clusterKeptRows M, (clusterRawReferenceLaw PT hPT hm).E
          (fun z => (PT.tiling.P i).M * clusterSigma PT hPT hm z.1 z.2 (M.positions r) x) ∧
      CS.binStage.historyLaw.E (clusterReferenceMean PT hPT hm i x M) ≤
        2 * rowMeanConstant κ ^ (clusterKeptRows M).card

/-- P15.4a: prove the row cap and nominal-denominator product comparison. -/
theorem high_cluster_row_caps (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) : ClusterRowCapClaim κ T := by
  have hWindow := HypercubeRamsey.Lane_q_s15_c2.clusterHighMode_degree_window hκ T
  let nR : ℕ → ℝ := fun k => (T.S.n k : ℝ)
  have hn : Tendsto nR atTop atTop :=
    (tendsto_natCast_atTop_atTop).comp T.S.n_tendsto
  have hpow : Tendsto (fun k => nR k ^ (0.96 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hn
  have hbstarEq : ∀ k, bstar T k = (nR k ^ (0.96 : ℝ))⁻¹ := by
    intro k
    dsimp [bstar, nR]
    rw [show (-1 + (0.04 : ℝ)) = -(0.96 : ℝ) by norm_num,
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ (T.S.n k : ℝ))]
  have hbstarTendsto : Tendsto (fun k => bstar T k) atTop (nhds 0) :=
    (tendsto_inv_atTop_zero.comp hpow).congr'
      (Filter.Eventually.of_forall fun k => (hbstarEq k).symm)
  have hbstar : ∀ᶠ k in atTop, bstar T k < 1 / 18 :=
    hbstarTendsto.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [hWindow, hbstar] with k hWindow hbstar
  intro PT hPT hm CS
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω a x
    exact CS.row_eq ω a x
  · sorry
  · sorry
  · intro i x hx b y
    let d := deg (T.S.E k) PT.tiling.c
      (PT.π (patchAt PT hPT b.1)).w x
    have herror : |d - 1 / 2| ≤ 1 / 6 := by
      by_cases hji : patchAt PT hPT b.1 = i
      · have hwindow := hWindow PT hPT hm i
        have h := hPT.envelope_degree i x hx
        have hown : |d - 1 / 2| ≤
            10 * Real.rpow ((PT.tiling.P i).q : ℝ) κ.Cb / (T.S.n k : ℝ) := by
          rcases hm with hs | hl
          · simpa [OwnDegOK, hs, hji, d] using h
          · simpa [OwnDegOK, hl, hji, d] using h
        exact hown.trans hwindow
      · have h := hPT.envelope_other_degree i (patchAt PT hPT b.1) hji x hx
        calc
          _ ≤ 3 * bstar T k := by simpa [d] using h
          _ ≤ 1 / 6 := by nlinarith [hbstar]
    have hdegree : 1 / 3 ≤ d := by
      have habs := abs_le.mp herror
      linarith
    have hden : 0 < d := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3) hdegree
    have hhit : hit (T.S.E k) PT.tiling.c x y ≤ 1 := by
      unfold hit
      split_ifs <;> norm_num
    unfold normalizedHit
    change (if 0 < d then
      hit (T.S.E k) PT.tiling.c x y / d else 0) ≤ 3
    rw [if_pos hden]
    apply (div_le_iff₀ hden).2
    have hthree : 1 ≤ 3 * d := by nlinarith
    nlinarith

/-- P15.4b: core removal counts, forest/rank sparsity and crossing-factor deletion. -/
theorem high_cluster_geometry (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) : ClusterGeometryClaim κ T := by
  sorry

set_option maxHeartbeats 1000000 in
/-- P15.4c: the small-bin core repeat cost. -/
theorem high_cluster_small_bin_splice (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) : ClusterSmallBinSpliceClaim κ T := by
  let A : ℝ := κ.a / 10 ^ 8
  let C : ℝ := Real.log 1600
  have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have hA : 0 < A := by dsimp [A]; positivity
  have hC : 0 < C := by dsimp [C]; exact Real.log_pos (by norm_num)
  have hMhiPos : 0 < (κ.Mhi : ℝ) := by
    have hnonneg : 0 ≤ (κ.Mhi : ℝ) := Nat.cast_nonneg _
    nlinarith [hκ.Mhi_big.2, hκ.cq_rng.1]
  have hMhiNat : 0 < κ.Mhi := by exact_mod_cast hMhiPos
  have hMhiOne : 1 ≤ (κ.Mhi : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hMhiNat))
  have hCb : 100 < κ.Cb := by
    have hratio : 0 < κ.aC / κ.aB := div_pos hκ.aC_rng.1 hκ.aB_rng.1
    have hterm : 0 < 100 * (κ.aC / κ.aB) := by positivity
    have hCbBig := hκ.Cb_big
    have hEq : (100 : ℝ) * κ.aC / κ.aB = 100 * (κ.aC / κ.aB) := by ring
    rw [hEq] at hCbBig
    linarith
  have hMloR : 0 < (κ.Mlo : ℝ) := by linarith [hκ.Mlo_big, hCb]
  have hMloNat : 0 < κ.Mlo := by exact_mod_cast hMloR
  have hMloOne : 1 ≤ (κ.Mlo : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hMloNat))
  have hcq : 0 < κ.cq := hκ.cq_rng.1
  have hcqLtOne : κ.cq < 1 := by
    have hden : 1 < 20 * (κ.Mlo : ℝ) := by nlinarith
    have hfrac : 1 / (20 * (κ.Mlo : ℝ)) < 1 := by
      simpa using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hden
    exact lt_trans hκ.cq_rng.2 hfrac
  have hMhiLower : 5 / κ.cq < (κ.Mhi : ℝ) := by
    have hbig := hκ.Mhi_big.2
    rw [mul_comm κ.cq (κ.Mhi : ℝ)] at hbig
    exact (div_lt_iff₀ hcq).2 hbig
  have hfiveDiv : 5 < 5 / κ.cq := by
    have h5cq : (5 : ℝ) * κ.cq < 5 := by
      have h := mul_lt_mul_of_pos_left hcqLtOne (show (0 : ℝ) < 5 by norm_num)
      simpa using h
    exact (lt_div_iff₀ hcq).2 h5cq
  have hMhiGtFive : 5 < (κ.Mhi : ℝ) := lt_trans hfiveDiv hMhiLower
  have hMhiMinusThree : 0 < (κ.Mhi : ℝ) - 3 := by linarith
  have hMhiMinusAC : 0 < (κ.Mhi : ℝ) - κ.aC := by
    have hAC : κ.aC < 1 := by
      have hmin : min κ.η0 1 / 10 ^ 6 ≤ (1 / 10 ^ 6 : ℝ) := by
        exact div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
      linarith [hκ.aC_rng.2, hmin]
    linarith
  let logN : ℕ → ℝ := fun k => Real.log (T.S.n k : ℝ)
  let qMin : ℕ → ℝ := fun k => (logN k) ^ κ.cq
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop).comp T.S.n_tendsto
  have ht : Tendsto logN atTop atTop := Real.tendsto_log_atTop.comp hn
  have hqMin : Tendsto qMin atTop atTop :=
    (tendsto_rpow_atTop hcq).comp ht
  have hpow4 : Tendsto (fun k => (logN k) ^ (4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp ht
  have hpowMhi : Tendsto (fun k => qMin k ^ (κ.Mhi : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop hMhiPos).comp hqMin
  have hpowMhiMinusThree : Tendsto
      (fun k => qMin k ^ ((κ.Mhi : ℝ) - 3)) atTop atTop :=
    (tendsto_rpow_atTop hMhiMinusThree).comp hqMin
  have hpowMhiMinusAC : Tendsto
      (fun k => qMin k ^ ((κ.Mhi : ℝ) - κ.aC)) atTop atTop :=
    (tendsto_rpow_atTop hMhiMinusAC).comp hqMin
  have hNratio : ∀ᶠ k in atTop,
      1 ≤ (T.S.N k : ℝ) / (2 : ℝ) ^ (T.S.n k) :=
    T.S.ratio_tendsto.eventually (eventually_ge_atTop (1 : ℝ))
  have htSmall : ∀ᶠ k in atTop, 1 ≤ logN k :=
    ht.eventually (eventually_ge_atTop (1 : ℝ))
  have htFourth : ∀ᶠ k in atTop, 20 / A ≤ (logN k) ^ (4 : ℝ) :=
    hpow4.eventually (eventually_ge_atTop (20 / A))
  have hqHeight : ∀ᶠ k in atTop, 4 * C / A ≤ qMin k ^ (κ.Mhi : ℝ) :=
    hpowMhi.eventually (eventually_ge_atTop (4 * C / A))
  have hqRank : ∀ᶠ k in atTop, 64 / A ≤ qMin k ^ ((κ.Mhi : ℝ) - 3) :=
    hpowMhiMinusThree.eventually (eventually_ge_atTop (64 / A))
  have hqAC : ∀ᶠ k in atTop, 4 / A ≤ qMin k ^ ((κ.Mhi : ℝ) - κ.aC) :=
    hpowMhiMinusAC.eventually (eventually_ge_atTop (4 / A))
  filter_upwards [hNratio, htSmall, htFourth, hqHeight, hqRank, hqAC]
      with k hNratioK ht1 ht4 hqHeightK hqRankK hqACK
  intro PT hPT hsmall i
  let t : ℝ := logN k
  let q : ℝ := (PT.tiling.P i).q
  let H : ℝ := (PT.tiling.P i).h
  let N : ℝ := T.S.N k
  let D : ℝ := (PT.tiling.P i).d
  let qmin : ℝ := qMin k
  rcases hPT.tiling_valid.cluster_data (Or.inr (Or.inl hsmall)) i with
    ⟨_, _, hMlower, hdf, _, _, _, hHlower, hHupper, _, hsmallIff, _⟩
  have hqreg := hsmallIff.mp hsmall
  have hqLower : t ^ κ.cq < q := by simpa [t, q, logN, qMin] using hqreg.1
  have hqUpper : q ≤ t ^ 2 := by simpa [t, q, logN] using hqreg.2
  have hqminLe : qmin ≤ q := by simpa [qmin, q, qMin, logN] using hqLower.le
  have hqOne : 1 ≤ q := by
    have hq0 : 1 ≤ t ^ κ.cq := Real.one_le_rpow ht1 (le_of_lt hcq)
    exact hq0.trans hqminLe
  have hHlower : q ^ (κ.Mhi : ℝ) ≤ H := by simpa [hsmall, q, H] using hHlower
  have hHupper : H < 2 * q ^ (κ.Mhi : ℝ) := by simpa [hsmall, q, H] using hHupper
  have htPow : t ^ (5 : ℝ) ≤ H := by
    have hBasePow : (t ^ κ.cq) ^ (κ.Mhi : ℝ) ≤ q ^ (κ.Mhi : ℝ) :=
      Real.rpow_le_rpow (by positivity) hqLower.le hMhiPos.le
    have hLogPow : t ^ (5 : ℝ) ≤ (t ^ κ.cq) ^ (κ.Mhi : ℝ) := by
      calc
        t ^ (5 : ℝ) ≤ t ^ (κ.cq * (κ.Mhi : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le ht1 (le_of_lt hκ.Mhi_big.2)
        _ = (t ^ κ.cq) ^ (κ.Mhi : ℝ) :=
          Real.rpow_mul (by positivity) κ.cq (κ.Mhi : ℝ)
    exact hLogPow.trans (hBasePow.trans hHlower)
  have hHone : 1 ≤ H := by
    have h1 : (1 : ℝ) ≤ t ^ (5 : ℝ) := Real.one_le_rpow ht1 (by norm_num)
    exact h1.trans htPow
  have hNpow : (2 : ℝ) ^ (T.S.n k) ≤ N := by
    have hpos : 0 < (2 : ℝ) ^ (T.S.n k) := by positivity
    have h := (le_div_iff₀ hpos).mp hNratioK
    simpa [N] using h
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hNpow
  let lowerM : ℝ := (1 / 400 : ℝ) * N * Real.exp (-q ^ κ.aC)
  have hMlower' : lowerM ≤ ((PT.tiling.P i).M : ℝ) := by simpa [lowerM, N, q] using hMlower
  have hMlowerPos : 0 < lowerM := by dsimp [lowerM]; positivity
  have hMpos : 0 < ((PT.tiling.P i).M : ℝ) := lt_of_lt_of_le hMlowerPos hMlower'
  have hDdiv : D / (PT.tiling.P i).M ≤ D / lowerM :=
    div_le_div_of_nonneg_left (by positivity) hMlowerPos hMlower'
  have hDivEq : D / lowerM = 400 * D / N * Real.exp (q ^ κ.aC) := by
    have hLowerInv : lowerM⁻¹ = 400 / N * Real.exp (q ^ κ.aC) := by
      dsimp [lowerM]
      rw [mul_inv, mul_inv]
      simp [div_eq_mul_inv, Real.exp_neg, hNpos.ne']
    rw [div_eq_mul_inv, hLowerInv]
    ring
  have hNinv : 1 / N ≤ (2 : ℝ) ^ (-(T.S.n k : ℤ)) := by
    have hInv := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : 0 < (2 : ℝ) ^ (T.S.n k)) hNpow
    calc
      _ ≤ 1 / (2 : ℝ) ^ (T.S.n k) := by simpa [N] using hInv
      _ = (2 : ℝ) ^ (-(T.S.n k : ℤ)) := by simp [zpow_neg, zpow_natCast]
  have hdfEq := hdf hsmall
  have hDupper : D ≤ Real.exp (Real.sqrt t) := by
    dsimp [D]
    rw [hdfEq]
    have hmin : ((min ⌊Real.exp (q / 2)⌋₊ ⌊Real.exp (Real.sqrt t)⌋₊ : ℕ) : ℝ) ≤
        (⌊Real.exp (Real.sqrt t)⌋₊ : ℝ) := by exact_mod_cast Nat.min_le_right _ _
    simpa only [Nat.cast_min] using hmin.trans (Nat.floor_le (Real.exp_nonneg _))
  rcases (hPT.tiling_valid.clique_scales i).1 (Or.inr (Or.inl hsmall)) with
    ⟨_, _, hQupper, hklt⟩
  have hkUpper : (PT.tiling.kScale i : ℝ) ≤ 2 * q ^ 2 := by
    have hkltR : (PT.tiling.kScale i : ℝ) < PT.tiling.Q i := by exact_mod_cast hklt
    have hQupperR : (PT.tiling.Q i : ℝ) ≤ 2 * q ^ 2 := by simpa [q] using hQupper
    linarith
  have hK : (PT.tiling.kScale i : ℝ) ≤ 2 * q ^ 2 := hkUpper
  have hMhiW : (κ.Mhi : ℝ) * κ.ω < 1 := by
    have hωProd := hκ.ω_rng.2
    have hAClt := hκ.aC_rng.2
    have hMinA : min κ.η0 1 ≤ 1 := min_le_right _ _
    have hsmallAC : κ.aC / 100 < 1 := by nlinarith [hAClt, hMinA]
    nlinarith [hωProd, hsmallAC]
  have hω : κ.ω ≤ 1 := by
    have hωProd := hκ.ω_rng.2
    have hωNonneg := hκ.ω_rng.1.le
    have hMhiOne := hMhiOne
    have hFactorNonneg : 0 ≤ (5 : ℝ) * κ.ω := mul_nonneg (by norm_num) hωNonneg
    have h5ω : 5 * κ.ω ≤ 5 * κ.ω * (κ.Mhi : ℝ) :=
      by simpa [mul_comm] using mul_le_mul_of_nonneg_left hMhiOne hFactorNonneg
    have hMinA : min κ.η0 1 ≤ 1 := min_le_right _ _
    have hMinAFraction : min κ.η0 1 / 10 ^ 6 ≤ (1 / 10 ^ 6 : ℝ) := by
      exact div_le_div_of_nonneg_right hMinA (by positivity)
    have hsmallAC : κ.aC / 100 < 1 := by
      have hACsmall : κ.aC < (1 / 10 ^ 6 : ℝ) := hκ.aC_rng.2.trans_le hMinAFraction
      nlinarith
    have hωprod1 : 5 * κ.ω < 1 := by
      calc
        5 * κ.ω ≤ 5 * κ.ω * (κ.Mhi : ℝ) := h5ω
        _ < κ.aC / 100 := hωProd
        _ < 1 := hsmallAC
    linarith [hωprod1]
  have hTwoω : (2 : ℝ) ^ κ.ω ≤ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (y := κ.ω)
          (z := (1 : ℝ)) (by norm_num) hω
      _ = 2 := Real.rpow_one _
  have hTscale : (PT.tiling.tScale i : ℝ) ≤ 4 * q := by
    have hceilArg : 1 ≤ H ^ κ.ω := Real.one_le_rpow hHone
      (le_of_lt hκ.ω_rng.1 : (0 : ℝ) ≤ κ.ω)
    have hceilNat : sliceT κ (PT.tiling.P i).h ≤ 2 * H ^ κ.ω := by
      have hhalf : (2 : ℝ)⁻¹ ≤ H ^ κ.ω :=
        (by norm_num : (2 : ℝ)⁻¹ ≤ 1).trans hceilArg
      have hceil := Nat.ceil_le_two_mul hhalf
      simpa [sliceT, H] using (show (Nat.ceil (H ^ κ.ω) : ℝ) ≤ 2 * H ^ κ.ω from by exact_mod_cast hceil)
    have hHeightR : H < 2 * q ^ (κ.Mhi : ℝ) := hHupper
    have hHpowlower : H ^ κ.ω ≤ (2 * q ^ (κ.Mhi : ℝ)) ^ κ.ω :=
      Real.rpow_le_rpow (by positivity) hHeightR.le (le_of_lt hκ.ω_rng.1)
    have hRpowSplit : (2 * q ^ (κ.Mhi : ℝ)) ^ κ.ω =
        (2 : ℝ) ^ κ.ω * q ^ ((κ.Mhi : ℝ) * κ.ω) := by
      rw [Real.mul_rpow (by norm_num) (by positivity),
        ← Real.rpow_mul (by positivity : 0 ≤ q)]
    have hQomega : q ^ ((κ.Mhi : ℝ) * κ.ω) ≤ q := by
      have hpow := Real.rpow_le_rpow_of_exponent_le hqOne hMhiW.le
      simpa [Real.rpow_one] using hpow
    have hTscale' : (PT.tiling.tScale i : ℝ) ≤ 2 * H ^ κ.ω := by
      simpa [Tiling.tScale] using hceilNat
    calc
      _ ≤ 2 * H ^ κ.ω := hTscale'
      _ ≤ 2 * ((2 * q ^ (κ.Mhi : ℝ)) ^ κ.ω) :=
        mul_le_mul_of_nonneg_left hHpowlower (by norm_num)
      _ = 2 * ((2 : ℝ) ^ κ.ω * q ^ ((κ.Mhi : ℝ) * κ.ω)) := by rw [hRpowSplit]
      _ ≤ 2 * (2 * q) := by gcongr
      _ = 4 * q := by ring
  have hKT : 2 * (PT.tiling.kScale i : ℝ) * (PT.tiling.tScale i : ℝ) ≤ 16 * q ^ 3 := by
    calc
      _ ≤ 2 * (2 * q ^ 2) * (4 * q) := by gcongr
      _ = 16 * q ^ 3 := by ring
  have htargetGain : (0.01 : ℝ) * PT.tiling.gain i = A * H := by
    simp [Tiling.gain, hsmall, A]
    ring
  have hG : C + 5 * t + 16 * q ^ 3 + q ^ κ.aC ≤ A * H := by
    have hconst : C ≤ (A / 4) * H := by
      have hscaled : C ≤ (A / 4) * qMin k ^ (κ.Mhi : ℝ) := by
        have hm := mul_le_mul_of_nonneg_right hqHeightK (by positivity : 0 ≤ A / 4)
        calc
          C = (4 * C / A) * (A / 4) := by dsimp [C, A]; field_simp [hA.ne']
          _ ≤ qMin k ^ (κ.Mhi : ℝ) * (A / 4) := hm
          _ = (A / 4) * qMin k ^ (κ.Mhi : ℝ) := by ring
      have hpow : qMin k ^ (κ.Mhi : ℝ) ≤ q ^ (κ.Mhi : ℝ) :=
        Real.rpow_le_rpow (by positivity) hqminLe hMhiPos.le
      have hh := mul_le_mul_of_nonneg_left (hpow.trans hHlower) (by positivity : 0 ≤ A / 4)
      exact hscaled.trans hh
    have htterm : 5 * t ≤ (A / 4) * H := by
      have hpow : t ^ (5 : ℝ) ≤ H := htPow
      have hscaled : 5 * t ≤ (A / 4) * t ^ (5 : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_right ht4 (by positivity : 0 ≤ A / 4)
        calc
          5 * t = (20 / A) * (A / 4) * t := by dsimp [A]; field_simp [hA.ne']; ring
          _ ≤ ((logN k) ^ (4 : ℝ) * (A / 4)) * t :=
            mul_le_mul_of_nonneg_right hmul (by positivity)
          _ = (A / 4) * t ^ (5 : ℝ) := by
            calc
              _ = (A / 4) * (t ^ (4 : ℝ) * t) := by ring
          _ = (A / 4) * t ^ (5 : ℝ) := by
                have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
                have hpow : Real.rpow t 4 * t = Real.rpow t 5 := by
                  have hadd := Real.rpow_add htpos (4 : ℝ) (1 : ℝ)
                  calc
                    _ = Real.rpow t 4 * Real.rpow t 1 :=
                      congrArg (fun z : ℝ => Real.rpow t 4 * z) (Real.rpow_one t).symm
                    _ = Real.rpow t (4 + 1) := hadd.symm
                    _ = Real.rpow t 5 := by congr 1 <;> norm_num
                exact congrArg (fun u : ℝ => (A / 4) * u) hpow
      exact hscaled.trans (mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ A / 4))
    have hq3term : 16 * q ^ 3 ≤ (A / 4) * H := by
      have hqMinPow : qMin k ^ ((κ.Mhi : ℝ) - 3) ≤ q ^ ((κ.Mhi : ℝ) - 3) :=
        Real.rpow_le_rpow (by positivity) hqminLe hMhiMinusThree.le
      have hmul := mul_le_mul_of_nonneg_right hqRankK (by positivity : 0 ≤ A / 4)
      have hpowEq : q ^ 3 * q ^ ((κ.Mhi : ℝ) - 3) = q ^ (κ.Mhi : ℝ) := by
        have hq3 : (q ^ (3 : ℕ) : ℝ) = Real.rpow q (3 : ℝ) :=
          (Real.rpow_natCast q 3).symm
        have hqTail : q ^ ((κ.Mhi : ℝ) - 3) =
            Real.rpow q ((κ.Mhi : ℝ) - 3) := rfl
        have hadd := Real.rpow_add (by linarith [hqOne] : 0 < q) (3 : ℝ)
          ((κ.Mhi : ℝ) - 3)
        have heq : (3 : ℝ) + ((κ.Mhi : ℝ) - 3) = (κ.Mhi : ℝ) := by ring
        rw [heq] at hadd
        calc
          _ = Real.rpow q 3 * Real.rpow q ((κ.Mhi : ℝ) - 3) := by rw [hq3, hqTail]
          _ = Real.rpow q (κ.Mhi : ℝ) := hadd.symm
      have hterm : 16 * q ^ 3 ≤ (A / 4) * q ^ (κ.Mhi : ℝ) := by
        have hq3nn : 0 ≤ q ^ 3 := by positivity
        have hmul' := mul_le_mul_of_nonneg_right hmul hq3nn
        have hscale : 16 * q ^ 3 = (64 / A * (A / 4)) * q ^ 3 := by
          dsimp [A]
          field_simp [hA.ne'] <;> ring
        calc
          _ = (64 / A * (A / 4)) * q ^ 3 := hscale
          _ ≤ (qMin k ^ ((κ.Mhi : ℝ) - 3) * (A / 4)) * q ^ 3 := hmul'
          _ = (A / 4) * (q ^ 3 * qMin k ^ ((κ.Mhi : ℝ) - 3)) := by ring
          _ ≤ (A / 4) * (q ^ 3 * q ^ ((κ.Mhi : ℝ) - 3)) := by gcongr
          _ = (A / 4) * q ^ (κ.Mhi : ℝ) := by rw [hpowEq]
      exact hterm.trans (mul_le_mul_of_nonneg_left hHlower (by positivity : 0 ≤ A / 4))
    have hqACTerm : q ^ κ.aC ≤ (A / 4) * H := by
      have hqMinPow : qMin k ^ ((κ.Mhi : ℝ) - κ.aC) ≤
          q ^ ((κ.Mhi : ℝ) - κ.aC) :=
        Real.rpow_le_rpow (by positivity) hqminLe hMhiMinusAC.le
      have hmul := mul_le_mul_of_nonneg_right hqACK (by positivity : 0 ≤ A / 4)
      have hpowEq : q ^ κ.aC * q ^ ((κ.Mhi : ℝ) - κ.aC) = q ^ (κ.Mhi : ℝ) := by
        have hadd := Real.rpow_add (by linarith [hqOne] : 0 < q) κ.aC
          ((κ.Mhi : ℝ) - κ.aC)
        have heq : κ.aC + ((κ.Mhi : ℝ) - κ.aC) = (κ.Mhi : ℝ) := by ring
        rw [heq] at hadd
        exact hadd.symm
      have hterm : q ^ κ.aC ≤ (A / 4) * q ^ (κ.Mhi : ℝ) := by
        have hqACnn : 0 ≤ q ^ κ.aC := by positivity
        have hmul' := mul_le_mul_of_nonneg_right hmul hqACnn
        have hscale : q ^ κ.aC = (4 / A * (A / 4)) * q ^ κ.aC := by
          dsimp [A]
          field_simp [hA.ne'] <;> ring
        calc
          _ = (4 / A * (A / 4)) * q ^ κ.aC := hscale
          _ ≤ (qMin k ^ ((κ.Mhi : ℝ) - κ.aC) * (A / 4)) * q ^ κ.aC := hmul'
          _ = (A / 4) * (q ^ κ.aC * qMin k ^ ((κ.Mhi : ℝ) - κ.aC)) := by ring
          _ ≤ (A / 4) * (q ^ κ.aC * q ^ ((κ.Mhi : ℝ) - κ.aC)) := by gcongr
          _ = (A / 4) * q ^ (κ.Mhi : ℝ) := by rw [hpowEq]
      exact hterm.trans (mul_le_mul_of_nonneg_left hHlower (by positivity : 0 ≤ A / 4))
    linarith
  have hFactorBound : 1600 * (T.S.n k : ℝ) ^ 4 * D *
      Real.exp (2 * (PT.tiling.kScale i : ℝ) * (PT.tiling.tScale i : ℝ) + q ^ κ.aC) ≤
      Real.exp (C + 4 * t + Real.sqrt t + 16 * q ^ 3 + q ^ κ.aC) := by
    have hn4 : (T.S.n k : ℝ) ^ 4 = Real.exp (4 * t) := by
      have hnexp : Real.exp t = (T.S.n k : ℝ) := by
        have hnpos : 0 < T.S.n k := by
          by_contra h
          have hz : T.S.n k = 0 := by omega
          simp [logN, hz] at ht1
          linarith
        dsimp [t, logN]
        exact Real.exp_log (by exact_mod_cast hnpos)
      calc
        _ = Real.exp t ^ 4 := by rw [← hnexp]
        _ = Real.exp (4 * t) := by rw [← Real.exp_nat_mul]; norm_num
    have h1600 : (1600 : ℝ) = Real.exp C := by dsimp [C]; rw [Real.exp_log (by norm_num)]
    calc
      _ = Real.exp C * Real.exp (4 * t) * D *
          Real.exp (2 * (PT.tiling.kScale i : ℝ) * (PT.tiling.tScale i : ℝ) + q ^ κ.aC) := by rw [h1600, hn4]
      _ ≤ Real.exp C * Real.exp (4 * t) * Real.exp (Real.sqrt t) *
          Real.exp (2 * (PT.tiling.kScale i : ℝ) * (PT.tiling.tScale i : ℝ) + q ^ κ.aC) := by gcongr
      _ ≤ Real.exp C * Real.exp (4 * t) * Real.exp (Real.sqrt t) *
          Real.exp (16 * q ^ 3 + q ^ κ.aC) := by
            apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hKT]))
            positivity
      _ = Real.exp (C + 4 * t + Real.sqrt t + 16 * q ^ 3 + q ^ κ.aC) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
  have hGupper : C + 4 * t + Real.sqrt t + 16 * q ^ 3 + q ^ κ.aC ≤ A * H := by
    have hsqrt : Real.sqrt t ≤ t := Real.sqrt_le_self_iff.mpr (Or.inr ht1)
    linarith [hG, hsqrt]
  have hCostSmall : clusterCoreRepeatCost PT i ≤
      (2 : ℝ) ^ (-(T.S.n k : ℤ)) * Real.exp (A * H) := by
    have hMlowerPos : 0 < lowerM := by dsimp [lowerM]; positivity
    have hDdiv : D / (PT.tiling.P i).M ≤ D / lowerM :=
      div_le_div_of_nonneg_left (by positivity) hMlowerPos hMlower
    have hNinv : 1 / N ≤ (2 : ℝ) ^ (-(T.S.n k : ℤ)) := by
      have hInv' := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
        (by positivity : 0 < (2 : ℝ) ^ (T.S.n k)) hNpow
      calc
        _ ≤ 1 / (2 : ℝ) ^ (T.S.n k) := by simpa [N] using hInv'
        _ = (2 : ℝ) ^ (-(T.S.n k : ℤ)) := by simp [zpow_neg, zpow_natCast]
    have hcostStep : clusterCoreRepeatCost PT i ≤
        (2 : ℝ) ^ (-(T.S.n k : ℤ)) *
          (1600 * (T.S.n k : ℝ) ^ 4 * D *
            Real.exp (2 * (PT.tiling.kScale i : ℝ) * (PT.tiling.tScale i : ℝ) + q ^ κ.aC)) := by
      unfold clusterCoreRepeatCost
      calc
        _ ≤ (T.S.n k : ℝ) ^ 4 * 4 *
            Real.exp (2 * (PT.tiling.kScale i : ℝ) * (PT.tiling.tScale i : ℝ)) *
              (D / lowerM) := by
                calc
                  _ = ((T.S.n k : ℝ) ^ 4 * 4 *
                      Real.exp (2 * (PT.tiling.kScale i : ℝ) * (PT.tiling.tScale i)) *
                      D) / (PT.tiling.P i).M := by ring
                  _ = ((T.S.n k : ℝ) ^ 4 * 4 *
                      Real.exp (2 * (PT.tiling.kScale i : ℝ) * (PT.tiling.tScale i))) *
                      (D / (PT.tiling.P i).M) := by ring
                  _ ≤ ((T.S.n k : ℝ) ^ 4 * 4 *
                      Real.exp (2 * (PT.tiling.kScale i : ℝ) * (PT.tiling.tScale i))) *
                      (D / lowerM) :=
                    mul_le_mul_of_nonneg_left hDdiv (by positivity)
        _ = (1 / N) *
            (1600 * (T.S.n k : ℝ) ^ 4 * D *
              Real.exp (2 * (PT.tiling.kScale i : ℝ) * (PT.tiling.tScale i : ℝ) + q ^ κ.aC)) := by
                rw [hDivEq, Real.exp_add]
                ring
        _ ≤ (2 : ℝ) ^ (-(T.S.n k : ℤ)) *
            (1600 * (T.S.n k : ℝ) ^ 4 * D *
              Real.exp (2 * (PT.tiling.kScale i : ℝ) * (PT.tiling.tScale i : ℝ) + q ^ κ.aC)) :=
            mul_le_mul_of_nonneg_right hNinv (by positivity)
    calc
      _ ≤ (2 : ℝ) ^ (-(T.S.n k : ℤ)) *
          (1600 * (T.S.n k : ℝ) ^ 4 * D *
            Real.exp (2 * (PT.tiling.kScale i : ℝ) * (PT.tiling.tScale i : ℝ) + q ^ κ.aC)) := hcostStep
      _ ≤ (2 : ℝ) ^ (-(T.S.n k : ℤ)) *
          Real.exp (C + 4 * t + Real.sqrt t + 16 * q ^ 3 + q ^ κ.aC) :=
            mul_le_mul_of_nonneg_left hFactorBound (by positivity)
      _ ≤ (2 : ℝ) ^ (-(T.S.n k : ℤ)) * Real.exp (A * H) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hGupper) (by positivity)
  have hGain : A * H = (0.01 : ℝ) * PT.tiling.gain i := by
    simp [A, Tiling.gain, hsmall]
    ring
  simpa [hGain] using hCostSmall

/-- P15.4d: transfer the actual masked product, conditional on its entering history and bins. -/
theorem high_cluster_label_transfer (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) : ClusterLabelTransfer κ T := by
  refine ⟨Real.exp 2, Real.exp_pos _, ?_⟩
  have hscaleEventually :=
    HypercubeRamsey.Lane_q_s15_c2.clusterHighSmall_height_degree_scale hκ T
  have hnEventually : ∀ᶠ k in atTop, 3 ≤ T.S.n k :=
    T.S.n_tendsto.eventually (eventually_ge_atTop 3)
  filter_upwards [hscaleEventually, hnEventually] with k hscaleK hn3
  intro PT hPT hm CS i x hx M hGeom
  have hcmp : ∀ W, CS.binStage.historyLaw.w W ≠ 0 →
      clusterHistoryLoad PT hPT hm W → ∀ B, (CS.binStage.binLaw W).w B ≠ 0 →
      ClusterMaskConsistent PT hPT hm M B →
        (CS.labelKernel W B).E (clusterKeptProduct PT hPT hm i x M W) ≤
          (2 * Real.exp (T.S.n k : ℝ)) *
            (clusterIndependentLabelKernel PT hPT hm W B).E
              (clusterKeptProduct PT hPT hm i x M W) := by
    intro W hW hload B hB hmask
    let S := HypercubeRamsey.Lane_q_s15_c2.clusterKeptProductScope hPT M
    let F : ClusterInternalData PT → ℝ :=
      fun I => clusterKeptProduct PT hPT hm i x M W I
    have hF : ∀ I, 0 ≤ F I := by
      intro I
      exact HypercubeRamsey.Lane_q_s15_c2.clusterKeptProduct_nonneg_of_data W I i x M
    have hdep := HypercubeRamsey.Lane_q_s15_c2.clusterKeptProduct_dependsOn_keptStarScope
      W i x M
    have hcard := HypercubeRamsey.Lane_q_s15_c2.clusterKeptProductScope_card_real_le hPT M
    by_cases hsmall : PT.tiling.mode = .highSmall
    · have hgood := CS.binStage.bin_requirements W hW hload B hB
      have hscale := hscaleK PT.tiling hPT.tiling_valid hsmall
      have hquery := HypercubeRamsey.Lane_q_s15_c2.clusterKeptProductScope_labelQueryOK
        hGeom B hgood hsmall hmask (fun j => (hscale j).2.1)
      have herror := HypercubeRamsey.Lane_q_s15_c2.clusterLabelError_le_exp_dimension
        hGeom B hgood hsmall hmask hscale
      exact HypercubeRamsey.Lane_q_s15_c2.clusterLabelKernel_le_of_localComparisons
        CS W hW hload B hB F S (Real.exp (T.S.n k : ℝ)) hF hdep hcard hquery herror
    · have hlarge : PT.tiling.mode = .highLarge := by
        rcases hm with hs | hl
        · exact (hsmall hs).elim
        · exact hl
      have hquery : ClusterLabelQueryOK PT hPT hm B S := by
        intro hsmall'
        exact (hsmall hsmall').elim
      have herror : clusterLabelError PT hPT hm B S ≤ Real.exp (T.S.n k : ℝ) := by
        have hnotSmall : PT.tiling.mode ≠ .highSmall := by
          intro hs
          rw [hs] at hlarge
          contradiction
        simp only [clusterLabelError, if_neg hnotSmall]
        have hnR : (1 : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast (by omega : 1 ≤ T.S.n k)
        have hexp := Real.add_one_le_exp (T.S.n k : ℝ)
        linarith
      exact HypercubeRamsey.Lane_q_s15_c2.clusterLabelKernel_le_of_localComparisons
        CS W hW hload B hB F S (Real.exp (T.S.n k : ℝ)) hF hdep hcard hquery herror
  have hmasked := HypercubeRamsey.Lane_q_s15_c2.clusterMaskedIntegral_le_of_labelComparison
    CS i x M (2 * Real.exp (T.S.n k : ℝ)) hcmp
  have hafter := HypercubeRamsey.Lane_q_s15_c2.clusterAfterLabelIntegral_nonneg CS i x M
  have hn1 : 1 ≤ T.S.n k := by omega
  have hfactor := HypercubeRamsey.Lane_q_s15_c2.two_exp_le_exp_two_pow
    (n := T.S.n k) hn1
  calc
    clusterMaskedIntegral CS i x M ≤
        (2 * Real.exp (T.S.n k : ℝ)) * clusterAfterLabelIntegral CS i x M := hmasked
    _ ≤ (Real.exp 2) ^ (T.S.n k) * clusterAfterLabelIntegral CS i x M :=
      mul_le_mul_of_nonneg_right hfactor hafter

/-- P15.4e: bin comparison and reverse integration, with all removed variables charged. -/
theorem high_cluster_bin_transfer (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) : ClusterBinTransfer κ T := by
  have hsmall : ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      PT.tiling.mode = .highSmall →
      ∀ i x, x ∈ PT.envelope i → ∀ M : ClusterMask PT, ClusterMaskGeometry PT hPT i M →
      ∀ W : ClusterHistory PT hPT hm,
      (clusterIndependentBinKernel PT hPT hm W).E
        (fun B => if ClusterMaskConsistent PT hPT hm M B then
          (clusterIndependentLabelKernel PT hPT hm W B).E
            (clusterKeptProduct PT hPT hm i x M W) else 0) ≤
        clusterCoreRepeatCost PT i ^ M.coreBins.card *
          clusterCrossingFraction T k ^ M.crossingBins.card *
            clusterReferenceMean PT hPT hm i x M W := by
    filter_upwards [high_cluster_small_bin_splice κ hκ T hDeep,
      Lane_sol_s15_transfer.eventual_core_radius κ hκ T,
      Lane_sol_s15_transfer.eventual_crossing_width κ hκ T,
      Lane_sol_s15_transfer.eventual_high_gain_le_dimension κ hκ T,
      T.S.n_tendsto.eventually (eventually_ge_atTop 1)] with k hs hr hw hg hn
    intro PT hPT hm hsmall i x hx M hM W
    exact Lane_sol_s15_transfer.raw_bin_repeat_bound_small PT hPT hm hsmall i x M hM
      (by nlinarith [hr PT hPT hm i]) hn (hw PT hPT)
      (Lane_sol_s15_transfer.crossing_bin_cap_of_splice PT hn (hg PT hPT hm) (hs PT hPT hsmall)) W
  filter_upwards [hsmall, T.S.n_tendsto.eventually (eventually_ge_atTop 5)] with k hk hn
  intro PT hPT hm CS i x hx M hM
  exact Lane_sol_s15_transfer.bin_transfer_of_scope_and_reverse PT hPT hm CS i x M
    (by omega) (Lane_sol_s15_transfer.maskBinQueries PT hPT hm M)
    (Lane_sol_s15_transfer.masked_label_integral_bin_depends PT hPT hm i x M)
    (Lane_sol_s15_transfer.mask_bin_queries_budget PT hPT hm M hn)
    (fun W => by
      rcases hm with hsm | hlg
      · exact hk PT hPT (Or.inl hsm) hsm i x hx M hM W
      · exact Lane_sol_s15_transfer.raw_bin_repeat_bound_large PT hPT (Or.inr hlg) hlg i x M W)

/-- P15.4f: restore the raw local scopes and factor the kept reference experiment. -/
theorem high_cluster_history_restore (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) : ClusterHistoryRestore κ T := by
  have hfactor : ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ i x, x ∈ PT.envelope i → ∀ M : ClusterMask PT, ClusterMaskGeometry PT hPT i M →
      (clusterHistoryLaw PT hPT hm).E (clusterReferenceMean PT hPT hm i x M) =
        ∏ r ∈ clusterKeptRows M, (clusterRawReferenceLaw PT hPT hm).E
          (fun z => (PT.tiling.P i).M * clusterSigma PT hPT hm z.1 z.2 (M.positions r) x) := by
    filter_upwards [Lane_sol_s15_transfer.eventual_core_radius κ hκ T,
      Lane_sol_s15_transfer.eventual_crossing_width κ hκ T,
      Lane_sol_s15_transfer.eventual_nominal_degrees_pos κ hκ T] with k hr hw hd
    intro PT hPT hm i x hx M hM
    exact Lane_sol_s15_transfer.raw_reference_factorization PT hPT hm i x M hM
      (hr PT hPT hm i) (hw PT hPT) (hd PT hPT hm i x hx)
  filter_upwards [hfactor, T.S.n_tendsto.eventually (eventually_ge_atTop 2)] with k hk hn
  intro PT hPT hm CS i x hx M hM
  exact Lane_sol_s15_transfer.history_restore_of_scope_and_factorization PT hPT hm CS i x M
    (by omega) (Lane_sol_s15_transfer.referenceConsultations PT hPT hm M)
    (Lane_sol_s15_transfer.reference_mean_history_depends PT hPT hm i x M)
    (Lane_sol_s15_transfer.reference_consultations_budget PT hPT hm M hn)
    hM.1 (hk PT hPT hm i x hx M hM)

/-- Fixed-mask expansion: caps and deletion costs are outside each nonnegative tested product. -/
def ClusterMaskExpansionClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    ∀ CS : ClusterSample PT hPT hm, ∀ i x, x ∈ PT.envelope i →
      clusterColumnMoment CS i x ≤
        (∑ M : ClusterMask PT, if ClusterMaskGeometry PT hPT i M then
          clusterMaskPayoff PT i M * clusterMaskedIntegral CS i x M else 0) /
          ((evenPatchPositions PT.tiling i).card : ℝ) ^ (T.S.n k)

/-- P15.4g(i): expand the column power and fix the ordered removal masks. -/
theorem high_cluster_mask_expansion (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04)
    (hcap : ClusterRowCapClaim κ T) (hgeometry : ClusterGeometryClaim κ T) :
    ClusterMaskExpansionClaim κ T := by
  classical
  filter_upwards [hcap, hgeometry] with k hcap hgeometry
  intro PT hPT hm CS i x hx
  obtain ⟨hroweq, hcap, hrow, hhit⟩ := hcap PT hPT hm CS
  obtain ⟨hcore, hrank, hnonisolated, hcross⟩ := hgeometry PT hPT hm
  let S := evenPatchPositions PT.tiling i
  let d : ℝ := (S.card : ℝ) ^ (T.S.n k)
  let Q := Fintype.piFinset (fun _ : Fin (T.S.n k) => S)
  let term := fun (M : ClusterMask PT) (ω : CS.Outcome) =>
    if ClusterMaskGeometry PT hPT i M then
      clusterMaskPayoff PT i M *
        (if CS.historyLoad ω ∧ ClusterMaskConsistent PT hPT hm M (CS.bins ω) then
          clusterKeptProduct PT hPT hm i x M (CS.history ω) (CS.internal ω) else 0)
    else 0
  have hterm0 : ∀ M ω, 0 ≤ term M ω := by
    intro M ω
    dsimp [term]
    split_ifs
    · exact mul_nonneg (Lane_sol_s15_mask.payoff_nonneg PT i M)
        (Lane_sol_s15_mask.keptProduct_nonneg PT hPT hm i x M _ _)
    all_goals simp
  have hinj (ω : CS.Outcome) : Function.Injective
      (fun vs => Lane_sol_s15_mask.orderedMask PT hPT hm i vs (CS.bins ω)) := by
    intro vs ws heq
    simpa only [Lane_sol_s15_mask.orderedMask_positions] using congrArg ClusterMask.positions heq
  have hpoint : ∀ ω, CS.law.w ω ≠ 0 →
      (if CS.historyLoad ω then clusterColumnAverage CS i x ω ^ (T.S.n k) else 0) ≤
        d⁻¹ * ∑ M, term M ω := by
    intro ω hw
    by_cases hload : CS.historyLoad ω
    · rw [if_pos hload]
      have htuple : (∑ vs ∈ Q, ∏ r, (PT.tiling.P i).M * CS.row ω (vs r) x) ≤
          ∑ M, term M ω := by
        calc
          (∑ vs ∈ Q, ∏ r, (PT.tiling.P i).M * CS.row ω (vs r) x) ≤
              ∑ vs ∈ Q, term (Lane_sol_s15_mask.orderedMask PT hPT hm i vs (CS.bins ω)) ω := by
            apply Finset.sum_le_sum
            intro vs hvs
            have hv : ∀ r, vs r ∈ S := Fintype.mem_piFinset.mp hvs
            let M := Lane_sol_s15_mask.orderedMask PT hPT hm i vs (CS.bins ω)
            have hM : ClusterMaskGeometry PT hPT i M :=
              Lane_sol_s15_mask.orderedMask_geometry PT hPT hm i vs (CS.bins ω) hv
            have hcons : ClusterMaskConsistent PT hPT hm M (CS.bins ω) :=
              Lane_sol_s15_mask.orderedMask_consistent PT hPT hm i vs (CS.bins ω)
            have hp := Lane_sol_s15_mask.masked_pointwise PT hPT hm CS i x M hM ω
              (hcap ω hw hload · x) (hrow ω hw hload · x) (hhit i x hx)
              (hcross i x hx M hM (CS.label ω))
            rw [show M.positions = vs from Lane_sol_s15_mask.orderedMask_positions PT hPT hm i vs (CS.bins ω)] at hp
            change (∏ r, (PT.tiling.P i).M * CS.row ω (vs r) x) ≤ term M ω
            dsimp only [term]
            rw [if_pos hM, if_pos (show CS.historyLoad ω ∧
              ClusterMaskConsistent PT hPT hm M (CS.bins ω) from ⟨hload, hcons⟩)]
            exact hp
          _ = ∑ M ∈ Q.image (fun vs => Lane_sol_s15_mask.orderedMask PT hPT hm i vs (CS.bins ω)),
              term M ω := by
            rw [Finset.sum_image]
            intro vs hvs ws hws heq
            exact hinj ω heq
          _ ≤ ∑ M, term M ω := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            intro M hM hnM
            exact hterm0 M ω
      change ((S.card : ℝ)⁻¹ * ∑ a ∈ S, (PT.tiling.P i).M * CS.row ω a x) ^ (T.S.n k) ≤ _
      rw [Lane_q_s15_c3.finset_average_pow_expand]
      exact mul_le_mul_of_nonneg_left htuple (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _))
    · rw [if_neg hload]
      exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _))
        (Finset.sum_nonneg fun M hM => hterm0 M ω)
  unfold clusterColumnMoment FinLaw.E
  calc
    (∑ ω, CS.law.w ω * (if CS.historyLoad ω then clusterColumnAverage CS i x ω ^ (T.S.n k) else 0)) ≤
        ∑ ω, d⁻¹ * ∑ M, CS.law.w ω * term M ω := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases hw : CS.law.w ω = 0
      · simp [hw]
      · have hh := mul_le_mul_of_nonneg_left (hpoint ω hw) (CS.law.nonneg ω)
        simpa only [Finset.mul_sum, mul_left_comm] using hh
    _ = d⁻¹ * ∑ M, ∑ ω, CS.law.w ω * term M ω := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ = (∑ M : ClusterMask PT, if ClusterMaskGeometry PT hPT i M then
        clusterMaskPayoff PT i M * clusterMaskedIntegral CS i x M else 0) /
        ((evenPatchPositions PT.tiling i).card : ℝ) ^ (T.S.n k) := by
      rw [div_eq_mul_inv, mul_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro M hM
      by_cases hgeom : ClusterMaskGeometry PT hPT i M
      · simp only [term, if_pos hgeom, clusterMaskedIntegral, FinLaw.E]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω hω
        ring
      · simp [term, hgeom]

/-- One fixed producer constant, shared with the final Markov estimate. -/
def ClusterColumnMomentBound (κ : CConsts) (T : Stage) (K : ℝ) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    ∀ CS : ClusterSample PT hPT hm, ∀ i x, x ∈ PT.envelope i →
      clusterColumnMoment CS i x ≤ K ^ (T.S.n k)

/-- P15.4: the paper supplies K before all sufficiently large indices and all tilings. -/
def ClusterColumnMomentClaim (κ : CConsts) (T : Stage) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ClusterColumnMomentBound κ T K

/-- P15.4g(ii): sum already-transferred masks and crossing forests.
All index-dependent estimates arrive as eventual contracts; no arbitrary early index is used. -/
theorem high_cluster_mask_summation (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04)
    (hexpand : ClusterMaskExpansionClaim κ T) (hgeometry : ClusterGeometryClaim κ T)
    (hsplice : ClusterSmallBinSpliceClaim κ T) (hlabel : ClusterLabelTransfer κ T)
    (hbin : ClusterBinTransfer κ T) (hhistory : ClusterHistoryRestore κ T) :
    ClusterColumnMomentClaim κ T := by
  classical
  obtain ⟨L, hL, hlabel⟩ := hlabel
  let D := max (rowMeanConstant κ) 1
  let K := (8 * Real.exp 1) * (16 * L * D)
  have hD : 1 ≤ D := le_max_right _ _
  have hD0 : 0 ≤ D := (by norm_num : (0 : ℝ) ≤ 1).trans hD
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [hexpand, hgeometry, hsplice, hlabel, hbin, hhistory,
    Lane_sol_s15_mask.eventually_high_gain_log hκ T,
    Lane_sol_s15_mask.eventually_crossing_costs hκ T,
    T.S.n_tendsto.eventually (eventually_ge_atTop 1)] with
      k hexpand hgeometry hsplice hlabel hbin hhistory hgain hcrosscost hn
  intro PT hPT hm CS i x hx
  by_cases hS : (evenPatchPositions PT.tiling i).Nonempty
  · let n := T.S.n k
    let A := Lane_sol_s15_mask.rowCap PT i
    let B := Lane_sol_s15_mask.coreCoefficient PT i
    let q := Lane_sol_s15_mask.crossingCoefficient PT
    let a : ℝ := 3 ^ (2 * (PT.tiling.P i).ℓ)
    let f := Real.exp (0.01 * PT.tiling.gain i) / 2 ^ n
    let F := 4 * (4 * L * D) ^ n
    let weight := fun M : ClusterMask PT =>
      A ^ M.geometric.card * B ^ M.coreBins.card * q ^ M.crossingBins.card *
        a ^ clusterCrossingRank PT M.positions M.geometric
    have hA : 0 ≤ A := by dsimp [A, Lane_sol_s15_mask.rowCap]; positivity
    have hB : 0 ≤ B := by
      dsimp [B, Lane_sol_s15_mask.coreCoefficient]
      split_ifs
      · exact mul_nonneg hA (Lane_sol_s15_mask.coreRepeatCost_nonneg PT i)
      · exact le_rfl
    have hq : 0 ≤ q := by
      dsimp [q, Lane_sol_s15_mask.crossingCoefficient]
      split_ifs <;> first | (unfold clusterCrossingFraction; positivity) | exact le_rfl
    have ha : 0 ≤ a := by dsimp [a]; positivity
    have hf : 0 ≤ f := by dsimp [f]; positivity
    have hF : 0 ≤ F := by dsimp [F]; positivity
    have hs : 0 ≤ PT.tiling.gain i := Lane_sol_s15_mask.high_gain_nonneg hκ PT hm i
    have hB1 : B ≤ 1 := by
      by_cases hmode : PT.tiling.mode = .highSmall
      · simp only [B, Lane_sol_s15_mask.coreCoefficient, if_pos hmode]
        exact Lane_sol_s15_mask.cap_repeat_bound PT i hs (hsplice PT hPT hmode i)
      · simp [B, Lane_sol_s15_mask.coreCoefficient, hmode]
    have hqsmall : q * (n : ℝ) ^ 2 ≤ 1 := by
      by_cases hmode : PT.tiling.mode = .highSmall
      · simpa only [q, Lane_sol_s15_mask.crossingCoefficient, if_pos hmode] using
          (hcrosscost PT hPT i).1
      · simp [q, Lane_sol_s15_mask.crossingCoefficient, hmode]
    have hgeomsmall : (n : ℝ) * f * A ≤ 1 :=
      Lane_sol_s15_mask.geometric_cap_bound PT i hn hs (hgain PT hPT hm i)
    obtain ⟨hcore, hrank, hnonisolated, hdelete⟩ := hgeometry PT hPT hm
    have hcore' : ∀ v ∈ evenPatchPositions PT.tiling i,
        (((evenPatchPositions PT.tiling i).filter (clusterCoreNear PT hPT i v)).card : ℝ) ≤
          f * (evenPatchPositions PT.tiling i).card := by
      intro v hv
      simpa only [f, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hcore i v hv
    have hrank' : ∀ G, (((evenPatchPositions PT.tiling i).card : ℝ) ^ n)⁻¹ *
        (∑ vs : Fin n → {v : EvenPosition T k // v ∈ evenPatchPositions PT.tiling i},
          a ^ clusterCrossingRank PT (fun r => (vs r).1) G) ≤ 2 := by
      intro G
      exact Lane_sol_s15_mask.rank_average_le_two PT i G a
        ((n : ℝ) ^ 2 * clusterCrossingFraction T k) ha (by unfold clusterCrossingFraction; positivity)
        (hcrosscost PT hPT i).2 (hrank i G)
    have hsum := Lane_sol_s15_mask.cluster_mask_weight_sum PT hPT i hS A B q a f
      hA hB hq ha hf hcore' hrank' hqsmall
    have hmean0 : 0 ≤ rowMeanConstant κ := by
      unfold rowMeanConstant
      exact mul_nonneg (div_nonneg (by norm_num) (Lane_sol_s15_mask.a_positive hκ).le) (by norm_num)
    have hpay : ∀ M, ClusterMaskGeometry PT hPT i M →
        clusterMaskPayoff PT i M * clusterMaskedIntegral CS i x M ≤ F * weight M := by
      intro M hM
      simpa only [F, weight, A, B, q, a, mul_assoc] using
        Lane_sol_s15_mask.transferred_payoff_bound PT hPT hm CS i x M L D hL.le hD
          hmean0 (le_max_left _ _) (hlabel PT hPT hm CS i x hx M hM)
          (hbin PT hPT hm CS i x hx M hM) (hhistory PT hPT hm CS i x hx M hM).2
    have hnumer : (∑ M : ClusterMask PT, if ClusterMaskGeometry PT hPT i M then
        clusterMaskPayoff PT i M * clusterMaskedIntegral CS i x M else 0) ≤
          F * ∑ M : ClusterMask PT, if ClusterMaskGeometry PT hPT i M then weight M else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro M hM
      by_cases hgeom : ClusterMaskGeometry PT hPT i M
      · simp only [if_pos hgeom]
        exact hpay M hgeom
      · simp [hgeom]
    have hpowB : (1 + B) ^ n ≤ (2 : ℝ) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hpowG : (1 + (n : ℝ) * f * A) ^ n ≤ (2 : ℝ) ^ n :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have hsmallSum : 2 * Real.exp 1 * (1 + B) ^ n * (1 + (n : ℝ) * f * A) ^ n ≤
        2 * Real.exp 1 * (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hpowB (by positivity)
      · exact hpowG
      · positivity
      · positivity
    have hconst : 1 ≤ 8 * Real.exp 1 := by
      have hh : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
      linarith
    have hconstpow : 8 * Real.exp 1 ≤ (8 * Real.exp 1) ^ n := by
      simpa only [pow_one] using pow_le_pow_right₀ hconst hn
    calc
      clusterColumnMoment CS i x ≤
          (∑ M : ClusterMask PT, if ClusterMaskGeometry PT hPT i M then
            clusterMaskPayoff PT i M * clusterMaskedIntegral CS i x M else 0) /
              ((evenPatchPositions PT.tiling i).card : ℝ) ^ n := hexpand PT hPT hm CS i x hx
      _ ≤ (F * ∑ M : ClusterMask PT, if ClusterMaskGeometry PT hPT i M then weight M else 0) /
          ((evenPatchPositions PT.tiling i).card : ℝ) ^ n :=
        div_le_div_of_nonneg_right hnumer (pow_nonneg (Nat.cast_nonneg _) _)
      _ = F * ((∑ M : ClusterMask PT, if ClusterMaskGeometry PT hPT i M then weight M else 0) /
          ((evenPatchPositions PT.tiling i).card : ℝ) ^ n) := by ring
      _ ≤ F * (2 * Real.exp 1 * (1 + B) ^ n * (1 + (n : ℝ) * f * A) ^ n) :=
        mul_le_mul_of_nonneg_left hsum hF
      _ ≤ F * (2 * Real.exp 1 * (2 : ℝ) ^ n * (2 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left hsmallSum hF
      _ = (8 * Real.exp 1) * (16 * L * D) ^ n := by
        dsimp only [F]
        have h16 : (16 : ℝ) ^ n = (4 : ℝ) ^ n * (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
          rw [← mul_pow, ← mul_pow]
          norm_num
        simp only [mul_pow]
        rw [h16]
        ring
      _ ≤ (8 * Real.exp 1) ^ n * (16 * L * D) ^ n :=
        mul_le_mul_of_nonneg_right hconstpow (by positivity)
      _ = K ^ n := by rw [← mul_pow]
  · have hempty : evenPatchPositions PT.tiling i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hmom : clusterColumnMoment CS i x = 0 := by
      simp [clusterColumnMoment, clusterColumnAverage, hempty, FinLaw.E,
        show T.S.n k ≠ 0 by omega]
    rw [hmom]
    exact pow_nonneg hK.le _

/-- P15.4: assemble the fixed-mask expansion, three actual transfers and mask summation. -/
theorem high_cluster_column_moment (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) : ClusterColumnMomentClaim κ T := by
  have hcap := high_cluster_row_caps κ hκ T hDeep
  have hgeometry := high_cluster_geometry κ hκ T hDeep
  have hsplice := high_cluster_small_bin_splice κ hκ T hDeep
  have hexpand := high_cluster_mask_expansion κ hκ T hDeep hcap hgeometry
  have hlabel := high_cluster_label_transfer κ hκ T hDeep
  have hbin := high_cluster_bin_transfer κ hκ T hDeep
  have hhistory := high_cluster_history_restore κ hκ T hDeep
  exact high_cluster_mask_summation κ hκ T hDeep hexpand hgeometry hsplice hlabel hbin hhistory

/-- Normalize one nonnegative high-cluster row after its mass gate. -/
noncomputable def clusterNormalizedSampleRow {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (CS : ClusterSample PT hPT hm) (ω : CS.Outcome)
    (a : EvenPosition T k) (x : Fin (T.S.N k)) : ℝ :=
  let m := ∑ z, CS.row ω a z
  if 0 < m then CS.row ω a x / m else 0

/-- The outcome guaranteed by P15.3a and the P15.4 Markov/union estimate. -/
def ClusterHallOutcomeClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    ∀ CS : ClusterSample PT hPT hm, ∃ ω, CS.law.w ω ≠ 0 ∧ CS.historyLoad ω ∧
      ∀ i x, x ∈ PT.envelope i →
        ∑ a ∈ evenPatchPositions PT.tiling i, CS.row ω a x ≤ 1 / 2

/-- C15.Fa: retain history-load success while applying Markov and the union bound to all columns. -/
theorem high_cluster_good_outcome (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (hSamples : ClusterSampleClaim κ T)
    (K : ℝ) (hK : 0 < K) (hMoments : ClusterColumnMomentBound κ T K) :
    ClusterHallOutcomeClaim κ T := by
  classical
  have hratio : ∀ᶠ k in atTop,
      160000 * K < (T.S.N k : ℝ) / (2 : ℝ) ^ (T.S.n k) := by
    filter_upwards [T.S.ratio_tendsto.eventually_ge_atTop (160000 * K + 1)] with k hk
    linarith
  have hdim : ∀ᶠ k in atTop, 4 ≤ T.S.n k :=
    T.S.n_tendsto.eventually_ge_atTop 4
  filter_upwards [hMoments, hratio, hdim] with k hmom hratioK hdimK
  intro PT hPT hm CS
  let n := T.S.n k
  let N := T.S.N k
  let t : ℝ := (N : ℝ) / (1600 * (2 : ℝ) ^ n)
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr (T.S.N_pos k)
  have hpowpos : 0 < (2 : ℝ) ^ n := by positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hKt : K / t < 1 / 100 := by
    have hratio' : 160000 * K * (2 : ℝ) ^ n < (N : ℝ) := by
      have h := (lt_div_iff₀ hpowpos).mp hratioK
      simpa [n, N, mul_assoc] using h
    dsimp [t]
    field_simp [ne_of_gt hpowpos, ne_of_gt hNpos]
    nlinarith
  have hSpos : 0 < (PT.tiling.S : ℝ) := by
    have hN : 0 < (T.S.N k : ℝ) := Nat.cast_pos.mpr (T.S.N_pos k)
    have hleft : 0 < (1 / 400 : ℝ) * (T.S.N k : ℝ) := by positivity
    exact lt_of_lt_of_le hleft hPT.tiling_valid.S_lower
  have hmass_div :
      (∑ i : Fin PT.tiling.m, (PT.tiling.P i).M : ℝ) / PT.tiling.S ≤ 1 := by
    calc
      (∑ i : Fin PT.tiling.m, (PT.tiling.P i).M : ℝ) / PT.tiling.S =
          ∑ i, ((PT.tiling.P i).M : ℝ) / PT.tiling.S := by
            rw [Finset.sum_div (s := Finset.univ)]
      _ ≤ ∑ i, (2 : ℝ) ^ (-((PT.tiling.P i).ℓ : ℤ)) := by
            apply Finset.sum_le_sum
            intro i hi
            exact hPT.tiling_valid.dyadic_mass_lower i
      _ = 1 := hPT.tiling_valid.dyadic_sum
  have hmass_sum :
      (∑ i : Fin PT.tiling.m, (PT.tiling.P i).M : ℝ) ≤ PT.tiling.S := by
    have h := (div_le_iff₀ hSpos).mp hmass_div
    nlinarith
  have hMpos : ∀ i : Fin PT.tiling.m, 0 < (PT.tiling.P i).M := by
    intro i
    have hx : 0 < (PT.tiling.P i).X.card :=
      Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1
    rw [(PT.tiling.P i).cardX] at hx
    exact hx
  have hm_sum : (PT.tiling.m : ℝ) ≤
      ∑ i : Fin PT.tiling.m, ((PT.tiling.P i).M : ℝ) := by
    calc
      (PT.tiling.m : ℝ) = ∑ i : Fin PT.tiling.m, (1 : ℝ) := by simp
      _ ≤ ∑ i : Fin PT.tiling.m, ((PT.tiling.P i).M : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact_mod_cast (Nat.succ_le_of_lt (hMpos i))
  have hm_le_N : PT.tiling.m ≤ N := by
    have hm_le_S : (PT.tiling.m : ℝ) ≤ PT.tiling.S := hm_sum.trans hmass_sum
    have hm_le_S_nat : PT.tiling.m ≤ PT.tiling.S := by exact_mod_cast hm_le_S
    exact hm_le_S_nat.trans hPT.tiling_valid.S_upper
  have hEll (i : Fin PT.tiling.m) : (PT.tiling.P i).ℓ ≤ n := by
    have hsup := Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ)
      (Finset.mem_univ i)
    have hprefix := hPT.tiling_valid.prefix_internal_length
    dsimp [n]
    omega
  have hEcard (i : Fin PT.tiling.m) :
      (evenPatchPositions PT.tiling i).card ≤ 2 ^ (n - (PT.tiling.P i).ℓ) := by
    apply HypercubeRamsey.Lane_q_s15_c3.even_prefix_card_le (PT.tiling.w i)
      (evenPatchPositions PT.tiling i) ?_ (hEll i)
    intro a ha j hj
    have hmem : a.1 ∈ PT.tiling.leaf i := by
      simpa [evenPatchPositions] using ha
    change ∀ j : Fin n, j.val < (PT.tiling.P i).ℓ → a.1 j = PT.tiling.w i j at hmem
    exact hmem j hj
  have hpatchratio (i : Fin PT.tiling.m)
      (hEpos : 0 < ((evenPatchPositions PT.tiling i).card : ℝ)) :
      (N : ℝ) / (1600 * (2 : ℝ) ^ n) ≤
        (PT.tiling.P i).M / (2 * (evenPatchPositions PT.tiling i).card) := by
    let u : ℝ := (2 : ℝ) ^ (-((PT.tiling.P i).ℓ : ℤ))
    have hu : 0 < u := by positivity
    have hpowNat :
        (2 : ℝ) ^ (n - (PT.tiling.P i).ℓ) * (2 : ℝ) ^ (PT.tiling.P i).ℓ =
          (2 : ℝ) ^ n := by
      rw [← pow_add, Nat.sub_add_cancel (hEll i)]
    have huinv : u = ((2 : ℝ) ^ (PT.tiling.P i).ℓ)⁻¹ := by
      dsimp [u]
      rw [zpow_neg, zpow_natCast]
    have hpow : (2 : ℝ) ^ n * u = (2 : ℝ) ^ (n - (PT.tiling.P i).ℓ) := by
      rw [huinv, ← hpowNat]
      field_simp
    have hEupper : ((evenPatchPositions PT.tiling i).card : ℝ) ≤
        (2 : ℝ) ^ n * u := by
      calc
        ((evenPatchPositions PT.tiling i).card : ℝ) ≤
            (2 : ℝ) ^ (n - (PT.tiling.P i).ℓ) := by exact_mod_cast hEcard i
        _ = (2 : ℝ) ^ n * u := hpow.symm
    have hSM : u * (PT.tiling.S : ℝ) < 2 * (PT.tiling.P i).M := by
      calc
        u * (PT.tiling.S : ℝ) <
            (2 * (PT.tiling.P i).M / PT.tiling.S) * PT.tiling.S :=
          mul_lt_mul_of_pos_right (by simpa [u] using hPT.tiling_valid.dyadic_mass_upper i) hSpos
        _ = 2 * (PT.tiling.P i).M := by field_simp [ne_of_gt hSpos]
    have hNscale :
        (N : ℝ) * u / 800 ≤ u * (PT.tiling.S : ℝ) / 2 := by
      have hs := mul_le_mul_of_nonneg_right hPT.tiling_valid.S_lower hu.le
      nlinarith
    have hMlower : (N : ℝ) * u / 800 < (PT.tiling.P i).M := by
      have hSM' : u * (PT.tiling.S : ℝ) / 2 < (PT.tiling.P i).M := by nlinarith
      exact lt_of_le_of_lt hNscale hSM'
    have hleft : (N : ℝ) * (2 * (evenPatchPositions PT.tiling i).card) ≤
        (N : ℝ) * (2 * (2 : ℝ) ^ n * u) := by
      calc
        _ = 2 * (N : ℝ) * (evenPatchPositions PT.tiling i).card := by ring
        _ ≤ 2 * (N : ℝ) * ((2 : ℝ) ^ n * u) :=
          mul_le_mul_of_nonneg_left hEupper (by positivity)
        _ = (N : ℝ) * (2 * (2 : ℝ) ^ n * u) := by ring
    have hright : (N : ℝ) * (2 * (2 : ℝ) ^ n * u) <
        (PT.tiling.P i).M * (1600 * (2 : ℝ) ^ n) := by
      have hmul := mul_lt_mul_of_pos_right hMlower (by positivity :
        0 < (1600 : ℝ) * (2 : ℝ) ^ n)
      calc
        (N : ℝ) * (2 * (2 : ℝ) ^ n * u) =
            ((N : ℝ) * u / 800) * (1600 * (2 : ℝ) ^ n) := by ring
        _ < (PT.tiling.P i).M * (1600 * (2 : ℝ) ^ n) := hmul
    have hcross := le_trans hleft hright.le
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    exact hcross
  have haverage_eq (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (ω : CS.Outcome) :
      clusterColumnAverage CS i x ω =
        ((PT.tiling.P i).M / (evenPatchPositions PT.tiling i).card) *
          ∑ a ∈ evenPatchPositions PT.tiling i, CS.row ω a x := by
    unfold clusterColumnAverage
    change ((evenPatchPositions PT.tiling i).card : ℝ)⁻¹ *
        ∑ a ∈ evenPatchPositions PT.tiling i, (PT.tiling.P i).M * CS.row ω a x = _
    calc
      _ = ((evenPatchPositions PT.tiling i).card : ℝ)⁻¹ *
          ((PT.tiling.P i).M *
            ∑ a ∈ evenPatchPositions PT.tiling i, CS.row ω a x) := by
              congr 1
              rw [← Finset.mul_sum]
      _ = _ := by ring
  have havg_nonneg (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (ω : CS.Outcome) :
      0 ≤ clusterColumnAverage CS i x ω := by
    unfold clusterColumnAverage
    apply mul_nonneg
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · apply Finset.sum_nonneg
      intro a ha
      exact mul_nonneg (by positivity) (CS.row_nonneg ω a x)
  have havg_large (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (ω : CS.Outcome)
      (hxi : x ∈ PT.envelope i)
      (hbad : 1 / 2 < ∑ a ∈ evenPatchPositions PT.tiling i, CS.row ω a x) :
      t < clusterColumnAverage CS i x ω := by
    have hEi : (evenPatchPositions PT.tiling i).Nonempty := by
      by_contra hempty
      have hEq := Finset.not_nonempty_iff_eq_empty.mp hempty
      rw [hEq, Finset.sum_empty] at hbad
      norm_num at hbad
    have hEpos : 0 < ((evenPatchPositions PT.tiling i).card : ℝ) :=
      Nat.cast_pos.mpr (Finset.card_pos.mpr hEi)
    have hMpos' : 0 < ((PT.tiling.P i).M : ℝ) := Nat.cast_pos.mpr (hMpos i)
    have hMEpos : 0 <
        ((PT.tiling.P i).M : ℝ) / ((evenPatchPositions PT.tiling i).card : ℝ) := by
      exact div_pos hMpos' hEpos
    have hmul : (((PT.tiling.P i).M : ℝ) / ((evenPatchPositions PT.tiling i).card : ℝ)) * (1 / 2) <
        (((PT.tiling.P i).M : ℝ) / ((evenPatchPositions PT.tiling i).card : ℝ)) *
          ∑ a ∈ evenPatchPositions PT.tiling i, CS.row ω a x :=
      mul_lt_mul_of_pos_left hbad hMEpos
    calc
      t ≤ (PT.tiling.P i).M / (2 * (evenPatchPositions PT.tiling i).card) :=
        hpatchratio i hEpos
      _ = ((PT.tiling.P i).M / (evenPatchPositions PT.tiling i).card) * (1 / 2) := by
        field_simp [ne_of_gt hEpos]
      _ < ((PT.tiling.P i).M / (evenPatchPositions PT.tiling i).card) *
          ∑ a ∈ evenPatchPositions PT.tiling i, CS.row ω a x := hmul
      _ = clusterColumnAverage CS i x ω := (haverage_eq i x ω).symm
  let Bad : (Fin PT.tiling.m × Fin N) → CS.Outcome → Prop := fun q ω =>
    q.2 ∈ PT.envelope q.1 ∧
      1 / 2 < ∑ a ∈ evenPatchPositions PT.tiling q.1, CS.row ω a q.2
  let BadAll : CS.Outcome → Prop := fun ω => ∃ q, Bad q ω
  have hbadprob (q : Fin PT.tiling.m × Fin N) :
      CS.law.pr (fun ω => CS.historyLoad ω ∧ Bad q ω) ≤ (1 / 100 : ℝ) ^ n := by
    by_cases hq : q.2 ∈ PT.envelope q.1
    · have hMarkov := HypercubeRamsey.Lane_q_s15_c3.finLaw_pr_markov
        CS.law CS.historyLoad (fun ω => clusterColumnAverage CS q.1 q.2 ω)
        (fun ω hω => havg_nonneg q.1 q.2 ω) t ht n
      have hMoment := hmom PT hPT hm CS q.1 q.2 hq
      calc
        CS.law.pr (fun ω => CS.historyLoad ω ∧ Bad q ω) ≤
            CS.law.pr (fun ω => CS.historyLoad ω ∧
              t < clusterColumnAverage CS q.1 q.2 ω) := by
                apply HypercubeRamsey.Lane_q_s15_c3.finLaw_pr_mono
                intro ω hω
                exact ⟨hω.1, havg_large q.1 q.2 ω hq hω.2.2⟩
        _ ≤ CS.law.E (fun ω => if CS.historyLoad ω then
              clusterColumnAverage CS q.1 q.2 ω ^ n else 0) / t ^ n := by
                simpa using hMarkov
        _ ≤ K ^ n / t ^ n := div_le_div_of_nonneg_right
              (by simpa [clusterColumnMoment] using hMoment) (pow_nonneg ht.le _)
        _ = (K / t) ^ n := (div_pow K t n).symm
        _ ≤ (1 / 100 : ℝ) ^ n :=
              pow_le_pow_left₀ (by positivity) (le_of_lt hKt) n
    · have hfalse : ∀ ω, ¬ Bad q ω := by
        intro ω h
        exact hq h.1
      have hzero : CS.law.pr (fun ω => CS.historyLoad ω ∧ Bad q ω) = 0 := by
        unfold FinLaw.pr
        apply Finset.sum_eq_zero
        intro ω hω
        simp [hfalse ω]
      rw [hzero]
      positivity
  have hbad_all : CS.law.pr (fun ω => CS.historyLoad ω ∧ BadAll ω) ≤ 1 / 2 := by
    calc
      CS.law.pr (fun ω => CS.historyLoad ω ∧ BadAll ω) =
          CS.law.pr (fun ω => ∃ q, CS.historyLoad ω ∧ Bad q ω) := by
            congr 1
            funext ω
            apply propext
            simp [BadAll]
      _ ≤ ∑ q, CS.law.pr (fun ω => CS.historyLoad ω ∧ Bad q ω) :=
          HypercubeRamsey.Lane_q_s15_c3.finLaw_pr_exists_le_sum CS.law
            (fun q ω => CS.historyLoad ω ∧ Bad q ω)
      _ ≤ ∑ q : Fin PT.tiling.m × Fin N, (1 / 100 : ℝ) ^ n :=
          Finset.sum_le_sum fun q hq => hbadprob q
      _ = (Fintype.card (Fin PT.tiling.m × Fin N) : ℝ) * (1 / 100 : ℝ) ^ n := by simp
      _ ≤ 1 / 2 := by
        have hNle : N ≤ n * 2 ^ n := by simpa [N, n] using T.S.N_le k
        have hmR : (PT.tiling.m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hm_le_N
        have hNR : (N : ℝ) ≤ (n : ℝ) * (2 : ℝ) ^ n := by exact_mod_cast hNle
        have hcount :
            (Fintype.card (Fin PT.tiling.m × Fin N) : ℝ) ≤
              (n : ℝ) ^ 2 * (4 : ℝ) ^ n := by
          simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
          calc
            (PT.tiling.m : ℝ) * (N : ℝ) ≤ (N : ℝ) * (N : ℝ) :=
              mul_le_mul_of_nonneg_right hmR (Nat.cast_nonneg _)
            _ ≤ ((n : ℝ) * (2 : ℝ) ^ n) * ((n : ℝ) * (2 : ℝ) ^ n) :=
              mul_le_mul hNR hNR (by positivity) (by positivity)
            _ = (n : ℝ) ^ 2 * (4 : ℝ) ^ n := by
              calc
                _ = (n : ℝ) ^ 2 * ((2 : ℝ) ^ n * (2 : ℝ) ^ n) := by ring
                _ = (n : ℝ) ^ 2 * (4 : ℝ) ^ n := by rw [← mul_pow]; norm_num
        have hpoly := HypercubeRamsey.Lane_q_s15_c3.nat_sq_le_two_pow n hdimK
        have hsmall : (n : ℝ) ^ 2 * (4 : ℝ) ^ n * (1 / 100 : ℝ) ^ n ≤ 1 / 2 := by
          calc
            _ = (n : ℝ) ^ 2 * ((4 : ℝ) ^ n * (1 / 100 : ℝ) ^ n) := by ring
            _ = (n : ℝ) ^ 2 * (4 / 100 : ℝ) ^ n := by
              congr 1
              rw [← mul_pow]
              congr 1
              norm_num
            _ ≤ (2 : ℝ) ^ n * (4 / 100 : ℝ) ^ n :=
              mul_le_mul_of_nonneg_right hpoly (by positivity)
            _ = (8 / 100 : ℝ) ^ n := by rw [← mul_pow]; norm_num
            _ ≤ (8 / 100 : ℝ) ^ 4 := by
              have hbase0 : 0 ≤ (8 / 100 : ℝ) := by norm_num
              have hbase1 : (8 / 100 : ℝ) ≤ 1 := by norm_num
              have htail : (8 / 100 : ℝ) ^ (n - 4) ≤ 1 := pow_le_one₀ hbase0 hbase1
              have hnEq : n = 4 + (n - 4) := by omega
              calc
                (8 / 100 : ℝ) ^ n = (8 / 100 : ℝ) ^ (4 + (n - 4)) := by
                  congr 1
                _ = (8 / 100 : ℝ) ^ 4 * (8 / 100 : ℝ) ^ (n - 4) := by rw [pow_add]
                _ ≤ (8 / 100 : ℝ) ^ 4 * 1 :=
                    mul_le_mul_of_nonneg_left htail (pow_nonneg hbase0 _)
                _ = (8 / 100 : ℝ) ^ 4 := by ring
            _ ≤ 1 / 2 := by norm_num
        exact (le_trans (mul_le_mul_of_nonneg_right hcount (by positivity)) hsmall)
  have hevent : CS.historyLoad =
        (fun ω => (CS.historyLoad ω ∧ ¬ BadAll ω) ∨
          (CS.historyLoad ω ∧ BadAll ω)) := by
    funext ω
    by_cases hload : CS.historyLoad ω
    · by_cases hbad : BadAll ω
      · simp [hload, hbad]
      · simp [hload, hbad]
    · simp [hload]
  have hdecomp : CS.law.pr CS.historyLoad ≤
      CS.law.pr (fun ω => CS.historyLoad ω ∧ ¬ BadAll ω) +
        CS.law.pr (fun ω => CS.historyLoad ω ∧ BadAll ω) := by
    calc
      CS.law.pr CS.historyLoad =
          CS.law.pr (fun ω => (CS.historyLoad ω ∧ ¬ BadAll ω) ∨
            (CS.historyLoad ω ∧ BadAll ω)) := congrArg CS.law.pr hevent
      _ ≤ _ := HypercubeRamsey.Lane_q_s15_c3.finLaw_pr_union CS.law _ _
  have hgoodpos : 0 < CS.law.pr (fun ω => CS.historyLoad ω ∧ ¬ BadAll ω) := by
    have hload := CS.history_load_probability
    linarith
  obtain ⟨ω, hω, hsuccess⟩ :=
    HypercubeRamsey.Lane_q_s15_c3.finLaw_pr_pos_exists CS.law
      (fun ω => CS.historyLoad ω ∧ ¬ BadAll ω) hgoodpos
  refine ⟨ω, hω, hsuccess.1, ?_⟩
  intro i x hx
  by_contra hbad
  apply hsuccess.2
  exact ⟨(i, x), hx, lt_of_not_ge hbad⟩

/-- A normalized set of even rows produced from one good cluster outcome. -/
structure ClusterHallCertificate {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (CS : ClusterSample PT hPT hm) (ω : CS.Outcome) where
  rows : DirectHallRows (T := T) (k := k) PT.tiling.c
  label_eq : rows.oddLabel = CS.label ω
  row_eq : rows.row = fun a x => clusterNormalizedSampleRow CS ω a x

/-- C15.Fb: normalize the rows from a passing cluster outcome and discharge Hall's hypotheses. -/
theorem high_cluster_fractional_rows {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid)
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (CS : ClusterSample PT hPT hm) (ω : CS.Outcome)
    (hinj : Function.Injective (CS.label ω))
    (hrow0 : ∀ a x, 0 ≤ CS.row ω a x)
    (hmass : ∀ a, (1 / 2 : ℝ) ≤ ∑ x, CS.row ω a x)
    (hlabel : ∀ b, CS.label ω b ∈ (PT.tiling.P (patchAt PT hPT b.1)).Y)
    (hsupp : ∀ a x, CS.row ω a x ≠ 0 →
      x ∈ PT.envelope (patchAt PT hPT a.1))
    (hcommon : ∀ a x, CS.row ω a x ≠ 0 → ∀ b, Adjacent a b →
      Hits (T.S.E k) PT.tiling.c x (CS.label ω b))
    (hcol : ∀ i x, x ∈ PT.envelope i →
      ∑ a ∈ evenPatchPositions PT.tiling i, CS.row ω a x ≤ 1 / 2) :
    Nonempty (ClusterHallCertificate CS ω) := by
  classical
  let mass : EvenPosition T k → ℝ := fun a => ∑ x, CS.row ω a x
  have hmass_pos : ∀ a, 0 < mass a := by
    intro a
    have hm := hmass a
    dsimp [mass] at *
    linarith
  have hrow_eq (a : EvenPosition T k) (x : Fin (T.S.N k)) :
      clusterNormalizedSampleRow CS ω a x = CS.row ω a x / mass a := by
    simp [clusterNormalizedSampleRow, mass, hmass_pos]
  have hpatch_mem (v : Position T k) :
      v ∈ PT.tiling.leaf (patchAt PT hPT v) := by
    exact (Classical.choose_spec (hPT.tiling_valid.prefix_complete v)).1
  have henvelope_unique (i j : Fin PT.tiling.m) (x : Fin (T.S.N k))
      (hi : x ∈ PT.envelope i) (hj : x ∈ PT.envelope j) : i = j := by
    by_contra hne
    have hdisj := hPT.tiling_valid.patch_X_disjoint i j hne
    have hxi : x ∈ (PT.tiling.P i).X := hPT.envelope_subset i hi
    have hxj : x ∈ (PT.tiling.P j).X := hPT.envelope_subset j hj
    exact (Finset.disjoint_left.mp hdisj) hxi hxj
  have hlabelY : ∀ b, CS.label ω b ∈ T.Y k := by
    intro b
    let i := patchAt PT hPT b.1
    have hy := hlabel b
    rcases hPT.tiling_valid.patch_supports i with ⟨_, _, hySub, hyResSub⟩
    exact (Finset.mem_sdiff.mp (hyResSub (hySub hy))).1
  refine ⟨⟨⟨CS.label ω, hinj, hlabelY,
    (fun a x => clusterNormalizedSampleRow CS ω a x), ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl⟩⟩
  · intro a x
    rw [hrow_eq]
    exact div_nonneg (hrow0 a x) (le_of_lt (hmass_pos a))
  · intro a
    simp_rw [hrow_eq]
    rw [← Finset.sum_div]
    change (∑ x, CS.row ω a x) / (∑ x, CS.row ω a x) = 1
    exact div_self (ne_of_gt (by linarith [hmass a]))
  · intro a x hne
    have hraw : CS.row ω a x ≠ 0 := by
      intro hz
      apply hne
      rw [hrow_eq, hz]
      simp
    have hx := hsupp a x hraw
    have hpatchX : x ∈ (PT.tiling.P (patchAt PT hPT a.1)).X :=
      hPT.envelope_subset (patchAt PT hPT a.1) hx
    rcases hPT.tiling_valid.patch_supports (patchAt PT hPT a.1) with
      ⟨hXres, hXhost, _, _⟩
    exact (Finset.mem_sdiff.mp (hXhost (hXres hpatchX))).1
  · intro a x hne b hab
    have hraw : CS.row ω a x ≠ 0 := by
      intro hz
      apply hne
      rw [hrow_eq, hz]
      simp
    exact hcommon a x hraw b hab
  · intro x
    by_cases hex : ∃ a, CS.row ω a x ≠ 0
    · obtain ⟨a₀, ha₀⟩ := hex
      let i := patchAt PT hPT a₀.1
      have hxenv : x ∈ PT.envelope i := by
        dsimp [i]
        exact hsupp a₀ x ha₀
      have hraw_out : ∀ a, a ∉ evenPatchPositions PT.tiling i → CS.row ω a x = 0 := by
        intro a hnot
        by_contra hne
        have hxenv' : x ∈ PT.envelope (patchAt PT hPT a.1) := hsupp a x hne
        have heq : patchAt PT hPT a.1 = i := henvelope_unique _ _ _ hxenv' hxenv
        apply hnot
        apply Finset.mem_filter.mpr
        constructor
        · simp
        · change a.1 ∈ PT.tiling.leaf i
          rw [← heq]
          exact hpatch_mem a.1
      have hsum_raw : (∑ a : EvenPosition T k, CS.row ω a x) =
          ∑ a ∈ evenPatchPositions PT.tiling i, CS.row ω a x := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro a ha hnot
        exact hraw_out a hnot
      have hsum_norm_le :
          (∑ a : EvenPosition T k, clusterNormalizedSampleRow CS ω a x) ≤
            2 * ∑ a : EvenPosition T k, CS.row ω a x := by
        calc
          _ ≤ ∑ a : EvenPosition T k, 2 * CS.row ω a x := by
            apply Finset.sum_le_sum
            intro a ha
            rw [hrow_eq]
            have hinv : (mass a)⁻¹ ≤ 2 := by
              have htwo : 1 ≤ 2 * mass a := by
                dsimp [mass]
                linarith [hmass a]
              rw [inv_eq_one_div]
              exact (div_le_iff₀ (hmass_pos a)).2 htwo
            calc
              CS.row ω a x / mass a = CS.row ω a x * (mass a)⁻¹ := by ring
              _ ≤ CS.row ω a x * 2 := mul_le_mul_of_nonneg_left hinv (hrow0 a x)
              _ = 2 * CS.row ω a x := by ring
          _ = 2 * ∑ a : EvenPosition T k, CS.row ω a x := by
            simp [Finset.mul_sum]
      have hlocal := hcol i x hxenv
      calc
        (∑ a : EvenPosition T k, clusterNormalizedSampleRow CS ω a x)
            ≤ 2 * ∑ a : EvenPosition T k, CS.row ω a x := hsum_norm_le
        _ = 2 * ∑ a ∈ evenPatchPositions PT.tiling i, CS.row ω a x := by rw [hsum_raw]
        _ ≤ 1 := by linarith
    · have hzero : ∀ a, CS.row ω a x = 0 := by
        intro a
        by_contra hne
        exact hex ⟨a, hne⟩
      have hsum_zero : (∑ a : EvenPosition T k, clusterNormalizedSampleRow CS ω a x) = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        rw [hrow_eq, hzero]
        simp
      rw [hsum_zero]
      norm_num

/-- C15.R applied to a normalized cluster certificate, retaining its sampler equations. -/
theorem cluster_certificate_to_cube {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    {CS : ClusterSample PT hPT hm} {ω : CS.Outcome}
    (H : ClusterHallCertificate CS ω) :
    CubeIn T k PT.tiling.c ∧ H.rows.oddLabel = CS.label ω ∧
      H.rows.row = fun a x => clusterNormalizedSampleRow CS ω a x := by
  have hRows := rows_to_cube PT.tiling.c H.rows
  exact ⟨hRows.1, H.label_eq, H.row_eq⟩

/-- C15.F converts the two high-cluster sampling modes into a cube. -/
theorem high_cluster_exclusion (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      (PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) → CubeIn T k PT.tiling.c := by
  have hSamples := high_cluster_sampling κ hκ T hDeep
  obtain ⟨K, hK, hMoments⟩ := high_cluster_column_moment κ hκ T hDeep
  have hGood := high_cluster_good_outcome κ hκ T hDeep hSamples K hK hMoments
  filter_upwards [hSamples, hGood] with k hSamplesK hGoodK
  intro PT hPT hm
  obtain ⟨CS⟩ := hSamplesK PT hPT hm
  obtain ⟨ω, hω, hload, hcol⟩ := hGoodK PT hPT hm CS
  obtain ⟨H⟩ := high_cluster_fractional_rows hPT (hm := hm) CS ω
    (CS.injective_on_support ω hω hload) (CS.row_nonneg ω) (CS.mass_gate ω hω hload)
    (CS.label_supported ω hω hload) (CS.row_support ω hω hload)
    (CS.common_neighbour ω hω hload) hcol
  exact (cluster_certificate_to_cube H).1

end HypercubeRamsey.S15
