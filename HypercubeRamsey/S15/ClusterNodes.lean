import HypercubeRamsey.S15.DirectNodes
import HypercubeRamsey.S15.Masks
import HypercubeRamsey.S15.Capacity
import HypercubeRamsey.S15.ClusterNodes_q_s15_c1

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
  sorry

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
  sorry

/-- P15.4b: core removal counts, forest/rank sparsity and crossing-factor deletion. -/
theorem high_cluster_geometry (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) : ClusterGeometryClaim κ T := by
  sorry

/-- P15.4c: the small-bin core repeat cost. -/
theorem high_cluster_small_bin_splice (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) : ClusterSmallBinSpliceClaim κ T := by
  sorry

/-- P15.4d: transfer the actual masked product, conditional on its entering history and bins. -/
theorem high_cluster_label_transfer (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) : ClusterLabelTransfer κ T := by
  sorry

/-- P15.4e: bin comparison and reverse integration, with all removed variables charged. -/
theorem high_cluster_bin_transfer (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) : ClusterBinTransfer κ T := by
  sorry

/-- P15.4f: restore the raw local scopes and factor the kept reference experiment. -/
theorem high_cluster_history_restore (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) : ClusterHistoryRestore κ T := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
