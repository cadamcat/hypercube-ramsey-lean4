import HypercubeRamsey.S15.Masks

namespace HypercubeRamsey.Lane_sol_s15_mask

open HypercubeRamsey.S15 Filter Classical
open scoped BigOperators

theorem a_positive {κ : CConsts} (hκ : κ.Admissible) : 0 < κ.a := by
  rw [hκ.a_eq]
  exact div_pos hκ.θ_rng.1 (by norm_num)

theorem high_gain_eq {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) (i : Fin PT.tiling.m) :
    PT.tiling.gain i = κ.a * (PT.tiling.P i).h / 10 ^ 6 := by
  rcases hm with h | h <;> simp only [Tiling.gain, h]

theorem high_gain_nonneg {κ : CConsts} (hκ : κ.Admissible) {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) (i : Fin PT.tiling.m) :
    0 ≤ PT.tiling.gain i := by
  rw [high_gain_eq PT hm i]
  exact div_nonneg (mul_nonneg (a_positive hκ).le (Nat.cast_nonneg _)) (by norm_num)

theorem eventually_high_gain_log {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, PT.Valid →
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ i, Real.log (T.S.n k : ℝ) ≤ PT.tiling.gain i := by
  have ha := a_positive hκ
  have hMlo : (1 : ℝ) ≤ κ.Mlo := by
    have hratio : 0 < 100 * κ.aC / κ.aB := div_pos (mul_pos (by norm_num) hκ.aC_rng.1) hκ.aB_rng.1
    linarith [hκ.Cb_big, hκ.Mlo_big]
  have hcq : κ.cq ≤ 2 := by
    have hbound : 1 / (20 * (κ.Mlo : ℝ)) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    linarith [hκ.cq_rng.2]
  have hlog : Tendsto (fun k => Real.log (T.S.n k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp T.S.n_tendsto)
  filter_upwards [hlog.eventually (eventually_ge_atTop (max 1 (10 ^ 6 / κ.a)))] with k hk
  intro PT hPT hm i
  let l := Real.log (T.S.n k : ℝ)
  have hl : (1 : ℝ) ≤ l := (le_max_left _ _).trans hk
  have hl0 : 0 ≤ l := (by norm_num : (0 : ℝ) ≤ 1).trans hl
  have hlbig : 10 ^ 6 / κ.a ≤ l := (le_max_right _ _).trans hk
  have hcluster : PT.tiling.mode = .lowCluster ∨ PT.tiling.mode = .highSmall ∨
      PT.tiling.mode = .highLarge := Or.inr hm
  obtain ⟨_, _, _, _, _, _, _, hh, _, _, hsmall, hlarge⟩ :=
    hPT.tiling_valid.cluster_data hcluster i
  have hnot : PT.tiling.mode ≠ .lowCluster := by
    rcases hm with hs | hs <;> simp [hs]
  have hh' : Real.rpow (PT.tiling.P i).q κ.Mhi ≤ ((PT.tiling.P i).h : ℝ) := by
    simpa only [if_neg hnot] using hh
  have hq : l ^ κ.cq ≤ (PT.tiling.P i).q := by
    rcases hm with hs | hs
    · exact ((hsmall.mp hs).1).le
    · calc
        l ^ κ.cq ≤ l ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hl hcq
        _ = l ^ 2 := Real.rpow_two _
        _ ≤ _ := (hlarge.mp hs).le
  have hheight : l ^ 5 ≤ ((PT.tiling.P i).h : ℝ) := by
    calc
      l ^ 5 = l ^ (5 : ℝ) := (Real.rpow_natCast _ 5).symm
      _ ≤ l ^ (κ.cq * κ.Mhi) :=
        Real.rpow_le_rpow_of_exponent_le hl hκ.Mhi_big.2.le
      _ = (l ^ κ.cq) ^ (κ.Mhi : ℝ) := Real.rpow_mul hl0 _ _
      _ ≤ (PT.tiling.P i).q ^ (κ.Mhi : ℝ) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hl0 _) hq (Nat.cast_nonneg _)
      _ ≤ _ := hh'
  have hl4 : l ≤ l ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hl (show 1 ≤ 4 by norm_num)
  have ha4 : 10 ^ 6 ≤ κ.a * l ^ 4 := by
    have hb := (div_le_iff₀ ha).mp (hlbig.trans hl4)
    nlinarith
  rw [high_gain_eq PT hm i]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 6)).mpr
  change l * 10 ^ 6 ≤ κ.a * (PT.tiling.P i).h
  have hhMul := mul_le_mul_of_nonneg_left hheight ha.le
  have hlMul := mul_le_mul_of_nonneg_right ha4 hl0
  rw [show l ^ 5 = l ^ 4 * l by ring] at hhMul
  nlinarith

theorem crossing_fraction_exp (T : Stage) (k : ℕ) :
    clusterCrossingFraction T k = Real.exp ((0.01 - Real.log 2) * (T.S.n k : ℝ)) := by
  unfold clusterCrossingFraction
  have htwo : (2 : ℝ) ^ (T.S.n k) = Real.exp ((T.S.n k : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [zpow_neg, zpow_natCast, htwo, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  ring

theorem prefix_factor_bound {κ : CConsts} (hκ : κ.Admissible) {T : Stage} {k : ℕ}
    (hn : 1000000 ≤ T.S.n k) (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (i : Fin PT.tiling.m) :
    (3 : ℝ) ^ (2 * (PT.tiling.P i).ℓ) ≤ Real.exp (0.01 * (T.S.n k : ℝ)) := by
  have hmin : min κ.xs (min κ.η0 (0.01 : ℝ)) ≤ 0.01 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hι : κ.ι ≤ 1 / 2 := by linarith [hκ.ι_rng.2]
  have hnR : (1 : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast (show 1 ≤ T.S.n k by omega)
  have hnBig : (1000000 : ℝ) ≤ T.S.n k := by exact_mod_cast hn
  have hℓ : ((PT.tiling.P i).ℓ : ℝ) ≤ (T.S.n k : ℝ) ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ (max (PT.tiling.P i).h (PT.tiling.P i).ℓ : ℝ) := by exact_mod_cast le_max_right _ _
      _ ≤ (T.S.n k : ℝ) ^ κ.ι := (hPT.tiling_valid.allocation_bounds i).1.le
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hnR hι
  have hsqrt : ((PT.tiling.P i).ℓ : ℝ) ≤ Real.sqrt (T.S.n k : ℝ) := by
    simpa only [Real.sqrt_eq_rpow] using hℓ
  have hroot : Real.sqrt (T.S.n k : ℝ) ≤ (T.S.n k : ℝ) / 1000 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at hh
    exact hh
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3), ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hℓsmall := hsqrt.trans hroot
  have hm := mul_le_mul_of_nonneg_right hlog3 (show (0 : ℝ) ≤ (2 * (PT.tiling.P i).ℓ : ℕ) from Nat.cast_nonneg _)
  push_cast at hm ⊢
  nlinarith

theorem eventually_crossing_costs {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, PT.Valid → ∀ i,
      3 * clusterCrossingFraction T k * (T.S.n k : ℝ) ^ 2 ≤ 1 ∧
      (3 : ℝ) ^ (2 * (PT.tiling.P i).ℓ) *
        ((T.S.n k : ℝ) ^ 2 * clusterCrossingFraction T k) ≤ 1 / 2 := by
  have hlim : Tendsto (fun k => (T.S.n k : ℝ) ^ 2 * Real.exp (-0.2 * (T.S.n k : ℝ)))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.rpow_two] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 0.2 (by norm_num)).comp
        (tendsto_natCast_atTop_atTop.comp T.S.n_tendsto)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)
    norm_num at hh
    linarith
  filter_upwards [hlim.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 10)),
    T.S.n_tendsto.eventually (eventually_ge_atTop 1000000)] with k hk hn
  intro PT hPT i
  have hn0 : (0 : ℝ) ≤ T.S.n k := Nat.cast_nonneg _
  have hprefix := prefix_factor_bound hκ hn PT hPT i
  have hfrac : clusterCrossingFraction T k ≤ Real.exp (-0.2 * (T.S.n k : ℝ)) := by
    rw [crossing_fraction_exp]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hprod : (3 : ℝ) ^ (2 * (PT.tiling.P i).ℓ) * clusterCrossingFraction T k ≤
      Real.exp (-0.2 * (T.S.n k : ℝ)) := by
    calc
      _ ≤ Real.exp (0.01 * (T.S.n k : ℝ)) * clusterCrossingFraction T k :=
        mul_le_mul_of_nonneg_right hprefix (by unfold clusterCrossingFraction; positivity)
      _ = Real.exp ((0.02 - Real.log 2) * (T.S.n k : ℝ)) := by
        rw [crossing_fraction_exp, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := by apply Real.exp_le_exp.mpr; nlinarith
  constructor
  · have hh := mul_le_mul_of_nonneg_right hfrac (pow_nonneg hn0 2)
    nlinarith
  · have hh := mul_le_mul_of_nonneg_right hprod (pow_nonneg hn0 2)
    nlinarith

end HypercubeRamsey.Lane_sol_s15_mask
