import HypercubeRamsey.S03.Clock.Model
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace HypercubeRamsey.Lane_sol_clock_s6

open Filter
open scoped Topology

theorem log_mul_rpow_tendsto {p : ℝ} (hp : p < 0) :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) * (n : ℝ) ^ p) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (by linarith : 0 < -p)).tendsto_div_nhds_zero
  have hn := h.comp tendsto_natCast_atTop_atTop
  apply hn.congr'
  filter_upwards [] with n
  change Real.log (n : ℝ) / (n : ℝ) ^ (-p) = Real.log (n : ℝ) * (n : ℝ) ^ p
  rw [Real.rpow_neg (Nat.cast_nonneg n) p, div_eq_mul_inv, inv_inv]

theorem rpow_ratio_tendsto {p q : ℝ} (hpq : p < q) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ p / (n : ℝ) ^ q) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (by linarith : 0 < q - p)).comp
    tendsto_natCast_atTop_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hn)
  change (n : ℝ) ^ (-(q - p)) = (n : ℝ) ^ p / (n : ℝ) ^ q
  rw [← Real.rpow_sub hn0]
  simp only [neg_sub]

theorem delta_mul_rpow_tendsto (p : ℝ) :
    Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) ^ 2)) * (n : ℝ) ^ p) atTop (𝓝 0) := by
  have hsquare : Tendsto (fun n : ℕ => (n : ℝ) ^ 2) atTop atTop := by
    simpa only [Function.comp_def, Real.rpow_two] using
      (tendsto_rpow_atTop (by norm_num : 0 < (2 : ℝ))).comp tendsto_natCast_atTop_atTop
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p / 2) 1 (by norm_num)).comp hsquare
  apply h.congr'
  filter_upwards [] with n
  simp only [Function.comp_def, neg_mul, one_mul]
  have hp : ((n : ℝ) ^ 2) ^ (p / 2) = (n : ℝ) ^ p := by
    rw [← Real.rpow_two, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    ring
  rw [hp, mul_comm]

noncomputable def deltaN (n : ℕ) : ℝ := Real.exp (-((n : ℝ) ^ 2))
noncomputable def horizonN (K : ℝ) (n : ℕ) : ℝ := K * Real.log (n : ℝ) + deltaN n
noncomputable def insertionCapN (K : ℝ) (n : ℕ) : ℝ := (K + 1) ^ 2 * Real.log (n : ℝ)

theorem deltaN_tendsto : Tendsto deltaN atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) ^ 2))) atTop (𝓝 0)
  simpa only [Real.rpow_zero, mul_one] using delta_mul_rpow_tendsto 0

theorem negative_rpow_tendsto {p : ℝ} (hp : p < 0) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ p) atTop (𝓝 0) := by
  simpa only [Function.comp_def, neg_neg] using
    (tendsto_rpow_neg_atTop (by linarith : 0 < -p)).comp tendsto_natCast_atTop_atTop

theorem horizon_insertion_rpow_tendsto (K : ℝ) {p : ℝ} (hp : p < 0) :
    Tendsto (fun n : ℕ => horizonN K n * insertionCapN K n * (n : ℝ) ^ p) atTop (𝓝 0) := by
  have hhalf := log_mul_rpow_tendsto (by linarith : p / 2 < 0)
  have hfull := log_mul_rpow_tendsto hp
  have h := ((hhalf.mul hhalf).const_mul (K * (K + 1) ^ 2)).add
    ((deltaN_tendsto.mul hfull).const_mul ((K + 1) ^ 2))
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hn)
  have hp : (n : ℝ) ^ (p / 2) * (n : ℝ) ^ (p / 2) = (n : ℝ) ^ p := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  dsimp [horizonN, insertionCapN]
  rw [← hp]
  ring

theorem horizon_delta_rpow_tendsto (K p : ℝ) :
    Tendsto (fun n : ℕ => horizonN K n * deltaN n * (n : ℝ) ^ p) atTop (𝓝 0) := by
  have hlog := log_mul_rpow_tendsto (by norm_num : (-1 : ℝ) < 0)
  have hfirst := (hlog.mul (delta_mul_rpow_tendsto (p + 1))).const_mul K
  have hsecond := deltaN_tendsto.mul (delta_mul_rpow_tendsto p)
  have h := hfirst.add hsecond
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hn)
  have hp : (n : ℝ) ^ (-1 : ℝ) * (n : ℝ) ^ (p + 1) = (n : ℝ) ^ p := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  dsimp [horizonN, deltaN]
  rw [← hp]
  ring

noncomputable def normalizedErrorN (B A K σ : ℝ) (n : ℕ) : ℝ :=
  2 * (2 * (n : ℝ) ^ (B + 3 * (B + K) - A) +
    (n : ℝ) ^ (3 * (B + K) - σ) +
    insertionCapN K n * (n : ℝ) ^ (3 * (B + K) - A) +
    horizonN K n * insertionCapN K n * (n : ℝ) ^ (3 * (B + K) - 2 * A) +
    2 * horizonN K n * deltaN n * (n : ℝ) ^ (3 * (B + K))) *
      Real.exp (3 * deltaN n)

theorem normalizedErrorN_tendsto (B A K σ : ℝ) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hA : 4 * B + 3 * K < A) (hA' : 3 * (B + K) < A)
    (hσ : 3 * (B + K) < σ) :
    Tendsto (normalizedErrorN B A K σ) atTop (𝓝 0) := by
  have h1 := (negative_rpow_tendsto (by linarith : B + 3 * (B + K) - A < 0)).const_mul 2
  have h2 := negative_rpow_tendsto (by linarith : 3 * (B + K) - σ < 0)
  have h3 := (log_mul_rpow_tendsto (by linarith : 3 * (B + K) - A < 0)).const_mul ((K + 1) ^ 2)
  have h4 := horizon_insertion_rpow_tendsto K (by linarith : 3 * (B + K) - 2 * A < 0)
  have h5 := (horizon_delta_rpow_tendsto K (3 * (B + K))).const_mul 2
  have hδ3 : Tendsto (fun n => 3 * deltaN n) atTop (𝓝 0) := by
    simpa only [mul_zero] using deltaN_tendsto.const_mul 3
  have he := (Real.continuous_exp.tendsto 0).comp hδ3
  have h := ((((h1.add h2).add h3).add h4).add h5).const_mul 2
  have hfinal := h.mul he
  change Tendsto (fun n => normalizedErrorN B A K σ n) atTop (𝓝 0)
  simpa [normalizedErrorN, insertionCapN, mul_assoc] using hfinal

theorem normalizedErrorN_identity (B A K σ : ℝ) (n : ℕ) (hn : 0 < (n : ℝ)) :
    normalizedErrorN B A K σ n =
      2 * (2 * (n : ℝ) ^ B * (n : ℝ) ^ (-A) + (n : ℝ) ^ (-σ) +
        insertionCapN K n * (n : ℝ) ^ (-A) +
        horizonN K n * (insertionCapN K n * ((n : ℝ) ^ (-A)) ^ 2 + 2 * deltaN n)) *
          Real.exp (3 * horizonN K n) * (n : ℝ) ^ (3 * B) := by
  have h1 : (n : ℝ) ^ B * (n : ℝ) ^ (-A) * (n : ℝ) ^ (3 * (B + K)) =
      (n : ℝ) ^ (B + 3 * (B + K) - A) := by
    rw [← Real.rpow_add hn, ← Real.rpow_add hn]
    congr 1
    ring
  have h2 : (n : ℝ) ^ (-σ) * (n : ℝ) ^ (3 * (B + K)) = (n : ℝ) ^ (3 * (B + K) - σ) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  have h3 : (n : ℝ) ^ (-A) * (n : ℝ) ^ (3 * (B + K)) = (n : ℝ) ^ (3 * (B + K) - A) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  have h4 : ((n : ℝ) ^ (-A)) ^ 2 * (n : ℝ) ^ (3 * (B + K)) =
      (n : ℝ) ^ (3 * (B + K) - 2 * A) := by
    rw [pow_two, ← Real.rpow_add hn, ← Real.rpow_add hn]
    congr 1
    ring
  have hscale : (n : ℝ) ^ (3 * K) * (n : ℝ) ^ (3 * B) = (n : ℝ) ^ (3 * (B + K)) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  have hexp : Real.exp (3 * horizonN K n) = Real.exp (3 * deltaN n) * (n : ℝ) ^ (3 * K) := by
    rw [Real.rpow_def_of_pos hn, ← Real.exp_add]
    congr 1
    dsimp [horizonN]
    ring
  unfold normalizedErrorN
  rw [hexp, ← h1, ← h2, ← h3, ← h4, ← hscale]
  ring

theorem eventual_error_budget (B A K σ : ℝ) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hA : 4 * B + 3 * K < A) (hA' : 3 * (B + K) < A) (hσ : 3 * (B + K) < σ) :
    ∀ᶠ n : ℕ in atTop,
      2 * (2 * (n : ℝ) ^ B * (n : ℝ) ^ (-A) + (n : ℝ) ^ (-σ) +
        insertionCapN K n * (n : ℝ) ^ (-A) +
        horizonN K n * (insertionCapN K n * ((n : ℝ) ^ (-A)) ^ 2 + 2 * deltaN n)) *
          Real.exp (3 * horizonN K n) ≤ (n : ℝ) ^ (-3 * B) := by
  have hsmall := (normalizedErrorN_tendsto B A K σ hB hK hA hA' hσ).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with n hs hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hn)
  rw [normalizedErrorN_identity B A K σ n hn0] at hs
  have hpow : 0 < (n : ℝ) ^ (3 * B) := Real.rpow_pos_of_pos hn0 _
  have hinv : (n : ℝ) ^ (-3 * B) = 1 / (n : ℝ) ^ (3 * B) := by
    rw [show -3 * B = -(3 * B) by ring, Real.rpow_neg hn0.le]
    rw [one_div]
  rw [hinv]
  exact (le_div_iff₀ hpow).mpr hs.le

theorem horizon_rpow_tendsto (K : ℝ) {p : ℝ} (hp : p < 0) :
    Tendsto (fun n : ℕ => horizonN K n * (n : ℝ) ^ p) atTop (𝓝 0) := by
  have h := ((log_mul_rpow_tendsto hp).const_mul K).add (delta_mul_rpow_tendsto p)
  simpa only [horizonN, deltaN, add_mul, mul_assoc, mul_zero, zero_add] using h

theorem denominator_rpow_tendsto (K σ : ℝ) (hσ : 0 < σ) {p : ℝ} (hp : p < 0) :
    Tendsto (fun n : ℕ => (horizonN K n + (n : ℝ) ^ (-σ) / 3) * (n : ℝ) ^ p) atTop (𝓝 0) := by
  have h := (horizon_rpow_tendsto K hp).add
    ((negative_rpow_tendsto (by linarith : p - σ < 0)).div_const 3)
  simp only [zero_div, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hn)
  have hp : (n : ℝ) ^ (-σ) * (n : ℝ) ^ p = (n : ℝ) ^ (p - σ) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  rw [← hp]
  ring

theorem failureExponent_ratio_tendsto (K C σ α β : ℝ) (hσ : 0 < σ)
    (hαβ : α < β) (h2β : 2 < β) :
    Tendsto (fun n : ℕ =>
      ((n : ℝ) ^ α + 2 * (n : ℝ) ^ 2 + |C| * (n : ℝ)) *
        (2 * (horizonN K n + (n : ℝ) ^ (-σ) / 3)) / (n : ℝ) ^ β) atTop (𝓝 0) := by
  have h1 := denominator_rpow_tendsto K σ hσ (by linarith : α - β < 0)
  have h2 := (denominator_rpow_tendsto K σ hσ (by linarith : 2 - β < 0)).const_mul 2
  have h3 := (denominator_rpow_tendsto K σ hσ (by linarith : 1 - β < 0)).const_mul |C|
  have h := ((h1.add h2).add h3).const_mul 2
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hn)
  have h1 := Real.rpow_sub hn0 α β
  have h2 := Real.rpow_sub hn0 2 β
  have h3 := Real.rpow_sub hn0 1 β
  rw [h1, h2, h3, Real.rpow_two, Real.rpow_one]
  ring

theorem eventual_failure_budget (K C σ α β : ℝ) (hK : 0 ≤ K) (hσ : 0 < σ)
    (hαβ : α < β) (h2β : 2 < β) :
    ∀ᶠ n : ℕ in atTop,
      4 * (horizonN K n + 2) * Real.exp ((n : ℝ) ^ 2 + C * (n : ℝ)) *
        Real.exp (-((n : ℝ) ^ β / (2 * (horizonN K n + (n : ℝ) ^ (-σ) / 3)))) ≤
          Real.exp (-((n : ℝ) ^ α)) := by
  have hr := (failureExponent_ratio_tendsto K C σ α β hσ hαβ h2β).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hpref : Tendsto (fun n : ℕ => 4 * (horizonN K n + 2) * deltaN n) atTop (𝓝 0) := by
    have h := ((horizon_delta_rpow_tendsto K 0).const_mul 4).add (deltaN_tendsto.const_mul 8)
    simp only [Real.rpow_zero, mul_one, mul_zero, zero_add] at h
    apply h.congr'
    filter_upwards [] with n
    ring
  have hprefSmall := hpref.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hr, hprefSmall, eventually_ge_atTop (1 : ℕ)] with n hratio hpre hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hn)
  have hnlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hH : 0 ≤ horizonN K n := by
    dsimp [horizonN, deltaN]
    positivity
  have hden : 0 < 2 * (horizonN K n + (n : ℝ) ^ (-σ) / 3) := by
    have hp := Real.rpow_pos_of_pos hn0 (-σ)
    linarith
  have hpow : 0 < (n : ℝ) ^ β := Real.rpow_pos_of_pos hn0 β
  have hproduct := (div_le_iff₀ hpow).mp hratio.le
  have hF : (n : ℝ) ^ α + 2 * (n : ℝ) ^ 2 + |C| * (n : ℝ) ≤
      (n : ℝ) ^ β / (2 * (horizonN K n + (n : ℝ) ^ (-σ) / 3)) :=
    (le_div_iff₀ hden).mpr (by simpa only [one_mul] using hproduct)
  have hδpos : 0 < deltaN n := Real.exp_pos _
  have hpre' : 4 * (horizonN K n + 2) ≤ Real.exp ((n : ℝ) ^ 2) := by
    have h := (le_div_iff₀ hδpos).mpr hpre.le
    simpa [deltaN, Real.exp_neg, one_div] using h
  have hC : C * (n : ℝ) ≤ |C| * (n : ℝ) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) hn0.le
  calc
    _ ≤ Real.exp ((n : ℝ) ^ 2) * Real.exp ((n : ℝ) ^ 2 + C * (n : ℝ)) *
          Real.exp (-((n : ℝ) ^ β / (2 * (horizonN K n + (n : ℝ) ^ (-σ) / 3)))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpre' (Real.exp_nonneg _)) (Real.exp_nonneg _)
    _ = Real.exp (2 * (n : ℝ) ^ 2 + C * (n : ℝ) -
          (n : ℝ) ^ β / (2 * (horizonN K n + (n : ℝ) ^ (-σ) / 3))) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-((n : ℝ) ^ α)) := by
      apply Real.exp_le_exp.mpr
      linarith

theorem freedman_exponent_identity (A σ H : ℝ) (n : ℕ) (hn : 0 < (n : ℝ)) :
    ((n : ℝ) ^ (-σ)) ^ 2 /
      (2 * (H * (n : ℝ) ^ (-A) + (n : ℝ) ^ (-A) * (n : ℝ) ^ (-σ) / 3)) =
      (n : ℝ) ^ (A - 2 * σ) / (2 * (H + (n : ℝ) ^ (-σ) / 3)) := by
  have ha : (n : ℝ) ^ (-A) ≠ 0 := (Real.rpow_pos_of_pos hn _).ne'
  have hp : ((n : ℝ) ^ (-σ)) ^ 2 = (n : ℝ) ^ (-A) * (n : ℝ) ^ (A - 2 * σ) := by
    rw [pow_two, ← Real.rpow_add hn, ← Real.rpow_add hn]
    congr 1
    ring
  have hf : 2 * (H * (n : ℝ) ^ (-A) + (n : ℝ) ^ (-A) * (n : ℝ) ^ (-σ) / 3) =
      (n : ℝ) ^ (-A) * (2 * (H + (n : ℝ) ^ (-σ) / 3)) := by ring
  rw [hp, hf, mul_div_mul_left _ _ ha]

end HypercubeRamsey.Lane_sol_clock_s6
