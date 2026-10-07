import HypercubeRamsey.S15.DirectNodes
import HypercubeRamsey.S15.Masks
import HypercubeRamsey.S15.Capacity

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
