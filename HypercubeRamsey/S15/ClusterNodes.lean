import HypercubeRamsey.S15.DirectNodes

/-! History alarms, cluster mass, and the conditional bin and label stages of Section 15. -/

namespace HypercubeRamsey.S15

open HypercubeRamsey Filter Classical
open scoped BigOperators

/-- A history test depends only on the primitive slice records in `S`. -/
def ClusterHistoryDependsOn {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (F : ClusterHistory PT hPT hm → ℝ) (S : Finset (ClusterRecordIndex PT hPT hm)) : Prop :=
  ∀ W W', (∀ r ∈ S, W r = W' r) → F W = F W'

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
      ∀ W, clusterCrossingRemovedMass PT hPT hm W a ≤ Real.exp (-0.01 * T.S.n k)

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
    (∀ W, 0 ≤ F W) → ∀ S : Finset (ClusterRecordIndex PT hPT hm),
      ClusterHistoryDependsOn F S → (S.card : ℝ) ≤ (T.S.n k : ℝ) ^ κ.Astar →
        law.E F ≤ (1 + 1 / (T.S.n k : ℝ)) * (clusterHistoryLaw PT hPT hm).E F

/-- The output contract of L15.2c. -/
def ClusterHistoryConditioningClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      Nonempty (ClusterHistoryConditioning PT hPT hm)

/-- L15.2d: the conditional high-cluster mass tail for every alarm-avoiding history. -/
def ClusterMassClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    ∀ W, clusterAlarmsAvoided PT hPT hm W → ∀ a : EvenPosition T k,
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
  sorry

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

/-- P15.3b: the independent bin law rarely violates the capacity-certificate gates. -/
def ClusterCapacityClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    ∀ W, clusterHistoryLoad PT hPT hm W → ∀ y,
      (clusterIndependentBinKernel PT hPT hm W).pr
        (fun B => κ.θ0 < clusterGivenBinColumn PT hPT hm W B y) ≤
          Real.exp (-κ.cChernoff * (κ.d0 : ℝ) ^ (0.4 : ℝ))

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

/-- P15.4a: cap of each cluster row on a successful history and assignment. -/
def ClusterRowCapClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    ∀ CS : ClusterSample PT hPT hm,
      (∀ ω a x, CS.row ω a x = clusterRowWeight PT hPT hm (CS.history ω) (CS.internal ω) a x) ∧
      (∀ ω, CS.law.w ω ≠ 0 → CS.historyLoad ω → ∀ a x,
        (PT.tiling.P (patchAt PT hPT a.1)).M * CS.row ω a x ≤
          2 ^ (T.S.n k) * Real.exp (-200 * PT.tiling.gain (patchAt PT hPT a.1)))

/-- Core scopes meet when their complementary words and inner words are close. -/
def clusterCoreNear {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (a b : EvenPosition T k) : Prop :=
  (hammingDist (outsideWord PT hPT i a.1) (outsideWord PT hPT i b.1) : ℝ) ≤ 4 ∧
  (hammingDist (internalWord PT hPT i a.1) (internalWord PT hPT i b.1) : ℝ) ≤
    100 * κ.ρ * (PT.tiling.P i).h

/-- P15.4b: geometric core-neighbour and crossing-graph sparsity. -/
def ClusterGeometryClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    ∀ i a, a ∈ evenPatchPositions PT.tiling i →
      ((evenPatchPositions PT.tiling i).filter fun b => clusterCoreNear PT hPT i a b).card ≤
        (evenPatchPositions PT.tiling i).card *
          Real.exp (0.01 * PT.tiling.gain i) / 2 ^ (T.S.n k)

/-- P15.4c: the small-bin core repeat cost is absorbed by the row cap. -/
def ClusterSmallBinSpliceClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    PT.tiling.mode = .highSmall → ∀ i,
      (T.S.n k : ℝ) ^ 4 * 4 * Real.exp
        (2 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i) *
        (PT.tiling.P i).d / (PT.tiling.P i).M ≤
          (2 : ℝ) ^ (-(T.S.n k : ℤ)) * Real.exp (0.01 * PT.tiling.gain i)

/-- P15.4d: label-stage upper comparison on at most `n^2` queried roles. -/
def ClusterLabelTransfer {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (CS : ClusterSample PT hPT hm) : Prop :=
  (CS.referenceLabelLaw = clusterRawOddLabelLaw PT hPT hm) ∧
    (∀ ω b, CS.label ω b =
      (CS.internal ω (clusterSliceAt PT hPT b.1)).2 (clusterWordAt PT hPT b.1)) ∧
    (∀ (F : OddAssignment T k → ℝ), (∀ ys, 0 ≤ F ys) →
      ∀ (S : Finset (OddPosition T k)),
      (∀ ys ys', (∀ b ∈ S, ys b = ys' b) → F ys = F ys') →
      (S.card : ℝ) ≤ (T.S.n k : ℝ) ^ 2 →
        (FinLaw.map CS.law CS.label).E F ≤
          Real.exp (∑ b ∈ S, Real.rpow
            (max ((PT.tiling.P (patchAt PT hPT b.1)).d : ℝ) 1) (-0.04)) *
            CS.referenceLabelLaw.E F)

/-- P15.4e: bin-stage upper comparison on every queried group scope. -/
def ClusterBinTransfer {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (CS : ClusterSample PT hPT hm) : Prop :=
  (∀ ω g, CS.bins ω g = (CS.internal ω g.1).1 g.2) ∧
  (∀ W B, CS.law.pr (fun ω => CS.history ω = W ∧ CS.bins ω = B) =
    (FinLaw.bind CS.binStage.historyLaw CS.binStage.binLaw).pr (fun wb => wb = (W, B))) ∧
  (∀ W, CS.binStage.historyLaw.w W ≠ 0 → ∀ B,
    (CS.binStage.binLaw W).w B ≠ 0 → clusterBinGood PT hPT hm W B) ∧
  (∀ W, CS.binStage.historyLaw.w W ≠ 0 →
    ∀ (F : ClusterBinAssignment PT → ℝ), (∀ B, 0 ≤ F B) →
    ∀ (S : Finset (ClusterGroupIndex PT)),
    ClusterBinDependsOn F S → (S.card : ℝ) ≤ (T.S.n k : ℝ) ^ 3 →
      (CS.binStage.binLaw W).E F ≤ (1 + 1 / (T.S.n k : ℝ)) *
        (clusterIndependentBinKernel PT hPT hm W).E F)

/-- P15.4f: history avoidance restores the raw product on separated local scopes. -/
def ClusterHistoryRestore {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (CS : ClusterSample PT hPT hm) : Prop :=
    (∀ ω, CS.historyLoad ω ↔ clusterHistoryLoad PT hPT hm (CS.history ω)) ∧
      (1 - (1 / 100 : ℝ) ≤ CS.law.pr CS.historyLoad) ∧
      (0 < (clusterHistoryLaw PT hPT hm).pr (clusterAlarmsAvoided PT hPT hm)) ∧
      (CS.binStage.historyLaw = clusterAvoidedHistoryLaw PT hPT hm CS.binStage.history_positive) ∧
      (∀ W, CS.binStage.historyLaw.w W ≠ 0 → clusterAlarmsAvoided PT hPT hm W) ∧
      ((99 / 100 : ℝ) ≤ CS.binStage.historyLaw.pr (fun W => clusterHistoryLoad PT hPT hm W)) ∧
      (∀ (F : ClusterHistory PT hPT hm → ℝ), (∀ W, 0 ≤ F W) →
        ∀ (S : Finset (ClusterRecordIndex PT hPT hm)),
        (∀ W W', (∀ r ∈ S, W r = W' r) → F W = F W') →
        (S.card : ℝ) ≤ (T.S.n k : ℝ) ^ κ.Astar →
          CS.binStage.historyLaw.E F ≤ (1 + 1 / (T.S.n k : ℝ)) *
            (clusterHistoryLaw PT hPT hm).E F)

/-- P15.4a: cap estimate from the D14 row cap and the successful high-mode gates. -/
theorem high_cluster_row_caps (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) : ClusterRowCapClaim κ T := by
  sorry

/-- P15.4b: geometric removal counts and crossing-graph sparsity. -/
theorem high_cluster_geometry (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) : ClusterGeometryClaim κ T := by
  sorry

/-- P15.4c: small-bin repeated-core splice bound in high-small mode. -/
theorem high_cluster_small_bin_splice (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) : ClusterSmallBinSpliceClaim κ T := by
  sorry

/-- P15.4d: extract the label comparison proved at the label-sampling stage. -/
theorem high_cluster_label_transfer {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (CS : ClusterSample PT hPT hm) : ClusterLabelTransfer CS :=
  ⟨CS.referenceLabelLaw_eq,
    CS.label_eq, CS.label_local_upper_comparison⟩

/-- P15.4e: extract the bin comparison proved at the bin-sampling stage. -/
theorem high_cluster_bin_transfer {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (CS : ClusterSample PT hPT hm) : ClusterBinTransfer CS :=
  ⟨CS.bins_eq, CS.bin_stage_marginal_eq,
    CS.binStage.bin_requirements, CS.binStage.local_upper_comparison⟩

/-- P15.4f: extract the history-local comparison from the conditioned process. -/
theorem high_cluster_history_restore {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (CS : ClusterSample PT hPT hm) : ClusterHistoryRestore CS :=
  ⟨CS.history_eq, CS.history_load_probability,
    CS.binStage.history_positive,
    CS.binStage.historyLaw_eq,
    CS.binStage.history_avoids_alarms,
    CS.binStage.history_load_probability,
    CS.binStage.history_local_upper_comparison⟩

/-- P15.4g: sum the geometric removal masks and transfer costs into the `K^n` moment bound. -/
theorem high_cluster_mask_summation (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    {k : ℕ} {PT : ProfiledTiling κ T k} (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (CS : ClusterSample PT hPT hm) (i : Fin PT.tiling.m) (x : Fin (T.S.N k))
    (hrowFormula : ∀ ω a x,
      CS.row ω a x = clusterRowWeight PT hPT hm (CS.history ω) (CS.internal ω) a x)
    (hcap : ∀ ω, CS.law.w ω ≠ 0 → CS.historyLoad ω →
      ∀ a x', (PT.tiling.P (patchAt PT hPT a.1)).M * CS.row ω a x' ≤
        2 ^ (T.S.n k) * Real.exp (-200 * PT.tiling.gain (patchAt PT hPT a.1)))
    (hgeometry : ∀ a, a ∈ evenPatchPositions PT.tiling i →
      ((evenPatchPositions PT.tiling i).filter fun b => clusterCoreNear PT hPT i a b).card ≤
        (evenPatchPositions PT.tiling i).card * Real.exp (0.01 * PT.tiling.gain i) /
          2 ^ (T.S.n k))
    (hsplice : PT.tiling.mode = .highSmall →
      (T.S.n k : ℝ) ^ 4 * 4 * Real.exp
        (2 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i) *
        (PT.tiling.P i).d / (PT.tiling.P i).M ≤
          (2 : ℝ) ^ (-(T.S.n k : ℤ)) * Real.exp (0.01 * PT.tiling.gain i))
    (hlabel : ClusterLabelTransfer CS) (hbin : ClusterBinTransfer CS)
    (hhistory : ClusterHistoryRestore CS) :
    clusterColumnMoment CS i x ≤ κ.A0 ^ (T.S.n k) := by
  sorry

/-- P15.4: high-cluster column moments under the history, bin, and label stages. -/
def ClusterColumnMomentClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    ∀ CS : ClusterSample PT hPT hm, ∀ i x, x ∈ PT.envelope i →
      clusterColumnMoment CS i x ≤ κ.A0 ^ (T.S.n k)

/-- P15.4: assemble the caps, geometric masks, three transfers, and final summation. -/
theorem high_cluster_column_moment (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) : ClusterColumnMomentClaim κ T := by
  have hcap := high_cluster_row_caps κ hκ T hDeep
  have hgeometry := high_cluster_geometry κ hκ T hDeep
  have hsplice := high_cluster_small_bin_splice κ hκ T hDeep
  filter_upwards [hcap, hgeometry, hsplice] with k hcap hgeometry hsplice
  intro PT hPT hm CS i x hx
  exact high_cluster_mask_summation κ hκ T hPT hm CS i x
    (fun ω a x' => (hcap PT hPT hm CS).1 ω a x')
    (fun ω hω hload a x' => (hcap PT hPT hm CS).2 ω hω hload a x')
    (by
      intro a ha
      exact hgeometry PT hPT hm i a ha)
    (fun hs => hsplice PT hPT hs i)
    (high_cluster_label_transfer CS) (high_cluster_bin_transfer CS)
    (high_cluster_history_restore CS)

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
    (hMoments : ClusterColumnMomentClaim κ T) : ClusterHallOutcomeClaim κ T := by
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
  have hMoments := high_cluster_column_moment κ hκ T hDeep
  have hGood := high_cluster_good_outcome κ hκ T hDeep hSamples hMoments
  filter_upwards [hSamples, hGood] with k hSamplesK hGoodK
  intro PT hPT hm
  obtain ⟨CS⟩ := hSamplesK PT hPT hm
  obtain ⟨ω, hω, hload, hcol⟩ := hGoodK PT hPT hm CS
  obtain ⟨H⟩ := high_cluster_fractional_rows hPT (hm := hm) CS ω
    (CS.injective_on_support ω hω) (CS.row_nonneg ω) (CS.mass_gate ω hω)
    (fun b => CS.label_supported ω b) (CS.row_support ω) (CS.common_neighbour ω) hcol
  exact (cluster_certificate_to_cube H).1

end HypercubeRamsey.S15
