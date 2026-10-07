import HypercubeRamsey.S15.MaskSummation_sol_s15_mask
import HypercubeRamsey.S15.MaskNumerics_sol_s15_mask

namespace HypercubeRamsey.Lane_sol_s15_mask

open HypercubeRamsey.S15 Classical
open scoped BigOperators

noncomputable def rowCap {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (i : Fin PT.tiling.m) : ℝ :=
  2 ^ (T.S.n k) * Real.exp (-200 * PT.tiling.gain i)

noncomputable def coreCoefficient {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (i : Fin PT.tiling.m) : ℝ :=
  if PT.tiling.mode = .highSmall then rowCap PT i * clusterCoreRepeatCost PT i else 0

noncomputable def crossingCoefficient {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) : ℝ :=
  if PT.tiling.mode = .highSmall then 3 * clusterCrossingFraction T k else 0

theorem transferred_payoff_bound {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (CS : ClusterSample PT hPT hm) (i : Fin PT.tiling.m) (x : Fin (T.S.N k))
    (M : ClusterMask PT) (L D : ℝ) (hL : 0 ≤ L) (hD : 1 ≤ D)
    (hmean : 0 ≤ rowMeanConstant κ) (hmeanD : rowMeanConstant κ ≤ D)
    (hlabel : clusterMaskedIntegral CS i x M ≤ L ^ (T.S.n k) * clusterAfterLabelIntegral CS i x M)
    (hbin : clusterAfterLabelIntegral CS i x M ≤
      2 * clusterCoreRepeatCost PT i ^ M.coreBins.card *
        clusterCrossingFraction T k ^ M.crossingBins.card *
          CS.binStage.historyLaw.E (clusterReferenceMean PT hPT hm i x M))
    (hhistory : CS.binStage.historyLaw.E (clusterReferenceMean PT hPT hm i x M) ≤
      2 * rowMeanConstant κ ^ (clusterKeptRows M).card) :
    clusterMaskPayoff PT i M * clusterMaskedIntegral CS i x M ≤
      4 * (4 * L * D) ^ (T.S.n k) *
        (rowCap PT i) ^ M.geometric.card * (coreCoefficient PT i) ^ M.coreBins.card *
          (crossingCoefficient PT) ^ M.crossingBins.card *
            ((3 : ℝ) ^ (2 * (PT.tiling.P i).ℓ)) ^
              clusterCrossingRank PT M.positions M.geometric := by
  have hcost := coreRepeatCost_nonneg PT i
  have hfrac : 0 ≤ clusterCrossingFraction T k := by unfold clusterCrossingFraction; positivity
  have hD0 : 0 ≤ D := (by norm_num : (0 : ℝ) ≤ 1).trans hD
  have hkept : (clusterKeptRows M).card ≤ T.S.n k := by
    simpa using Finset.card_le_card (Finset.subset_univ (clusterKeptRows M))
  have hmeanpow : rowMeanConstant κ ^ (clusterKeptRows M).card ≤ D ^ (T.S.n k) :=
    (pow_le_pow_left₀ hmean hmeanD _).trans (pow_le_pow_right₀ hD hkept)
  have hhist := hhistory.trans (mul_le_mul_of_nonneg_left hmeanpow (by norm_num))
  have hraw : clusterMaskedIntegral CS i x M ≤
      4 * L ^ (T.S.n k) * clusterCoreRepeatCost PT i ^ M.coreBins.card *
        clusterCrossingFraction T k ^ M.crossingBins.card * D ^ (T.S.n k) := by
    calc
      _ ≤ L ^ (T.S.n k) * clusterAfterLabelIntegral CS i x M := hlabel
      _ ≤ L ^ (T.S.n k) *
          (2 * clusterCoreRepeatCost PT i ^ M.coreBins.card *
            clusterCrossingFraction T k ^ M.crossingBins.card *
              CS.binStage.historyLaw.E (clusterReferenceMean PT hPT hm i x M)) :=
        mul_le_mul_of_nonneg_left hbin (pow_nonneg hL _)
      _ ≤ L ^ (T.S.n k) *
          (2 * clusterCoreRepeatCost PT i ^ M.coreBins.card *
            clusterCrossingFraction T k ^ M.crossingBins.card * (2 * D ^ (T.S.n k))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hhist (by positivity)) (pow_nonneg hL _)
      _ = _ := by ring
  have hpay := mul_le_mul_of_nonneg_left hraw (payoff_nonneg PT i M)
  have hJ : 2 * clusterCrossingRank PT M.positions M.geometric * (PT.tiling.P i).ℓ =
      (2 * (PT.tiling.P i).ℓ) * clusterCrossingRank PT M.positions M.geometric := by ring
  have heq : clusterMaskPayoff PT i M *
      (4 * L ^ (T.S.n k) * clusterCoreRepeatCost PT i ^ M.coreBins.card *
        clusterCrossingFraction T k ^ M.crossingBins.card * D ^ (T.S.n k)) =
      4 * (4 * L * D) ^ (T.S.n k) * (rowCap PT i) ^ M.geometric.card *
        (rowCap PT i * clusterCoreRepeatCost PT i) ^ M.coreBins.card *
          (3 * clusterCrossingFraction T k) ^ M.crossingBins.card *
            ((3 : ℝ) ^ (2 * (PT.tiling.P i).ℓ)) ^
              clusterCrossingRank PT M.positions M.geometric := by
    unfold clusterMaskPayoff rowCap
    rw [hJ]
    simp only [mul_pow, pow_add, pow_mul]
    ring
  rw [heq] at hpay
  by_cases hs : PT.tiling.mode = .highSmall
  · simpa only [coreCoefficient, crossingCoefficient, if_pos hs] using hpay
  · by_cases hM : M.coreBins = ∅ ∧ M.crossingBins = ∅
    · simpa only [coreCoefficient, crossingCoefficient, if_neg hs, hM.1, hM.2,
        Finset.card_empty, pow_zero, mul_one] using hpay
    · have hne : M.coreBins ≠ ∅ ∨ M.crossingBins ≠ ∅ := by tauto
      rw [masked_integral_large_zero CS i x M hs hne, mul_zero]
      simp only [coreCoefficient, crossingCoefficient, if_neg hs]
      unfold rowCap
      positivity

theorem cap_repeat_bound {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (i : Fin PT.tiling.m)
    (hs : 0 ≤ PT.tiling.gain i)
    (hc : clusterCoreRepeatCost PT i ≤
      (2 : ℝ) ^ (-(T.S.n k : ℤ)) * Real.exp (0.01 * PT.tiling.gain i)) :
    rowCap PT i * clusterCoreRepeatCost PT i ≤ 1 := by
  have hcap : 0 ≤ rowCap PT i := by unfold rowCap; positivity
  calc
    _ ≤ rowCap PT i * ((2 : ℝ) ^ (-(T.S.n k : ℤ)) * Real.exp (0.01 * PT.tiling.gain i)) :=
      mul_le_mul_of_nonneg_left hc hcap
    _ = Real.exp (-199.99 * PT.tiling.gain i) := by
      unfold rowCap
      rw [zpow_neg, zpow_natCast]
      have htwo : (2 : ℝ) ^ (T.S.n k) ≠ 0 := pow_ne_zero _ (by norm_num)
      calc
        _ = Real.exp (-200 * PT.tiling.gain i) * Real.exp (0.01 * PT.tiling.gain i) := by
          field_simp
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith

theorem geometric_cap_bound {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (i : Fin PT.tiling.m) (hn : 1 ≤ T.S.n k)
    (hs : 0 ≤ PT.tiling.gain i) (hlog : Real.log (T.S.n k : ℝ) ≤ PT.tiling.gain i) :
    (T.S.n k : ℝ) * (Real.exp (0.01 * PT.tiling.gain i) / 2 ^ (T.S.n k)) * rowCap PT i ≤ 1 := by
  have hnR : (0 : ℝ) < T.S.n k := by exact_mod_cast (show 0 < T.S.n k by omega)
  calc
    _ = (T.S.n k : ℝ) * Real.exp (-199.99 * PT.tiling.gain i) := by
      unfold rowCap
      have htwo : (2 : ℝ) ^ (T.S.n k) ≠ 0 := pow_ne_zero _ (by norm_num)
      calc
        _ = (T.S.n k : ℝ) * (Real.exp (0.01 * PT.tiling.gain i) * Real.exp (-200 * PT.tiling.gain i)) := by
          field_simp
        _ = _ := by rw [← Real.exp_add]; congr 2; ring
    _ ≤ (T.S.n k : ℝ) * Real.exp (-Real.log (T.S.n k : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hnR.le
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = 1 := by rw [Real.exp_neg, Real.exp_log hnR]; exact mul_inv_cancel₀ hnR.ne'

end HypercubeRamsey.Lane_sol_s15_mask
