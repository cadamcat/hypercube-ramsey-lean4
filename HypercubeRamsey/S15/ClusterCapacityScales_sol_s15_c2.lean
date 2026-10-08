import HypercubeRamsey.S15.ClusterNodes_q_s15_c2

namespace HypercubeRamsey.Lane_sol_s15_c2

open HypercubeRamsey.S15 Classical Filter
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem high_degree_ge_log_ten (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      (PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) → ∀ i,
        (Real.log (T.S.n k : ℝ)) ^ (10 : ℝ) ≤ (PT.tiling.P i).d := by
  let t := fun k => Real.log (T.S.n k : ℝ)
  have ht : Tendsto t atTop atTop := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp T.S.n_tendsto)
  have hratio := (tendsto_exp_mul_div_rpow_atTop (10 : ℝ) (1 / 2) (by norm_num)).comp ht
  have hSmall := Lane_q_s15_c2.clusterHighSmall_height_degree_scale hκ T
  have hHeight := Lane_q_s15_c2.clusterHighMode_height_ge_log_fifth hκ T
  filter_upwards [hSmall, hHeight, ht.eventually_ge_atTop 1, hratio.eventually_ge_atTop 2]
      with k hSmall hHeight ht1 hratio
  intro PT hPT hm i
  have ht0 : 0 ≤ t k := (by norm_num : (0 : ℝ) ≤ 1).trans ht1
  rcases hm with hs | hl
  · have hheight := hHeight PT hPT (Or.inl hs) i
    have hdegree := (hSmall PT.tiling hPT.tiling_valid hs i).1
    have hpow : (t k) ^ (0.05 : ℝ) ≤ ((PT.tiling.P i).d : ℝ) ^ (0.005 : ℝ) := by
      calc
        _ ≤ (t k) ^ (5 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
        _ ≤ (PT.tiling.P i).h := by simpa [t, Real.rpow_natCast] using hheight
        _ ≤ _ := hdegree
    have hraise := Real.rpow_le_rpow (Real.rpow_nonneg ht0 _) hpow (by norm_num : (0 : ℝ) ≤ 200)
    rw [← Real.rpow_mul ht0, ← Real.rpow_mul (Nat.cast_nonneg (PT.tiling.P i).d)] at hraise
    rw [show (0.05 : ℝ) * 200 = 10 by norm_num,
      show (0.005 : ℝ) * 200 = 1 by norm_num, Real.rpow_one] at hraise
    exact hraise
  · obtain ⟨_, _, _, _, hd, _, _, _, _, _, _, hlarge⟩ :=
      hPT.tiling_valid.cluster_data (Or.inr (Or.inr hl)) i
    have hq : (t k) ^ (2 : ℕ) < (PT.tiling.P i).q := hlarge.mp hl
    have htq : t k ≤ (PT.tiling.P i).q := by
      have hsq : t k ≤ (t k) ^ (2 : ℕ) := by nlinarith only [ht1]
      exact hsq.trans hq.le
    have htpow : 0 < (t k) ^ (10 : ℝ) := Real.rpow_pos_of_pos (by linarith only [ht1]) _
    have hexp : 2 * (t k) ^ (10 : ℝ) ≤ Real.exp ((PT.tiling.P i).q / 2) := by
      have hlin : 2 * (t k) ^ (10 : ℝ) ≤ Real.exp ((1 / 2 : ℝ) * t k) :=
        (le_div_iff₀ htpow).mp hratio
      exact hlin.trans (Real.exp_le_exp.mpr (by linarith only [htq]))
    have htwo : 2 ≤ Real.exp ((PT.tiling.P i).q / 2) :=
      (by nlinarith only [Real.one_le_rpow ht1 (by norm_num : (0 : ℝ) ≤ 10)] : 2 ≤ 2 * (t k) ^ (10 : ℝ)).trans hexp
    have hfloor := Nat.lt_floor_add_one (Real.exp ((PT.tiling.P i).q / 2))
    have hhalf : Real.exp ((PT.tiling.P i).q / 2) / 2 ≤ (⌊Real.exp ((PT.tiling.P i).q / 2)⌋₊ : ℝ) := by
      linarith only [hfloor, htwo]
    have hd' := hd (Or.inr hl)
    rw [hd']
    linarith only [hexp, hhalf]

theorem high_capacity_charge_tail (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (c A : ℝ) (hc : 0 < c) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      (PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) →
      ∀ i (D : Bin PT.tiling i), Real.exp (-c * (D.1.card : ℝ) ^ (0.4 : ℝ)) ≤
        (T.S.n k : ℝ) ^ (-A) := by
  let t := fun k => Real.log (T.S.n k : ℝ)
  have ht : Tendsto t atTop atTop := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp T.S.n_tendsto)
  have ht3 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3)).comp ht
  filter_upwards [high_degree_ge_log_ten κ hκ T, ht.eventually_ge_atTop 1,
    ht3.eventually_ge_atTop (A / c)] with k hd ht1 ht3
  intro PT hPT hm i D
  have ht0 : 0 ≤ t k := (by norm_num : (0 : ℝ) ≤ 1).trans ht1
  have hD : (t k) ^ (10 : ℝ) ≤ (D.1.card : ℝ) := by
    rw [hPT.tiling_valid.bins_card i D.1 D.2]
    exact hd PT hPT hm i
  have hpow : (t k) ^ (4 : ℝ) ≤ (D.1.card : ℝ) ^ (0.4 : ℝ) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg ht0 _) hD (by norm_num : (0 : ℝ) ≤ 0.4)
    rw [← Real.rpow_mul ht0] at h
    rw [show (10 : ℝ) * 0.4 = 4 by norm_num] at h
    exact h
  have hA : A ≤ c * (t k) ^ (3 : ℝ) := by
    change A / c ≤ (t k) ^ (3 : ℝ) at ht3
    have h := (div_le_iff₀ hc).mp ht3
    nlinarith only [h]
  have hprod : A * t k ≤ c * (t k) ^ (4 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hA ht0
    have hmul : (t k) ^ (3 : ℝ) * t k = (t k) ^ (4 : ℝ) := by
      rw [show (4 : ℝ) = 3 + 1 by norm_num,
        Real.rpow_add (by linarith only [ht1] : 0 < t k), Real.rpow_one]
    calc
      A * t k ≤ (c * (t k) ^ (3 : ℝ)) * t k := h
      _ = c * (t k) ^ (4 : ℝ) := by rw [mul_assoc, hmul]
  have hnpos : (0 : ℝ) < T.S.n k := by
    have hn1 : 1 < (T.S.n k : ℝ) :=
      (Real.log_pos_iff (Nat.cast_nonneg (T.S.n k))).mp (by change 0 < t k; linarith only [ht1])
    linarith only [hn1]
  calc
    _ ≤ Real.exp (-c * (t k) ^ (4 : ℝ)) := Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hpow hc.le])
    _ ≤ Real.exp (-A * t k) := Real.exp_le_exp.mpr (by nlinarith only [hprod])
    _ = (T.S.n k : ℝ) ^ (-A) := by
      rw [Real.rpow_def_of_pos hnpos]
      congr 1
      dsimp [t]
      ring

end HypercubeRamsey.Lane_sol_s15_c2
