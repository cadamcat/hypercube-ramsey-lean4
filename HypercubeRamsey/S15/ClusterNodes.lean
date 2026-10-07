import HypercubeRamsey.S15.DirectNodes
import HypercubeRamsey.S15.Masks
import HypercubeRamsey.S15.Capacity
import HypercubeRamsey.S15.ClusterNodes_q_s15_c2

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
