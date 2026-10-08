import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d2_scale

namespace HypercubeRamsey.Lane_sol_s10_d2

open Classical OAI.HypercubeRamsey HypercubeRamsey.S10 Filter
open scoped BigOperators

/-- A superlinear negative exponent absorbs a full-cube union and any polynomial. -/
theorem cube_exp_error_small (a b C D ε : ℝ) (ha : 1 < a) (hC : 0 < C)
    (hD : 0 < D) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      D * (n : ℝ) ^ b * (2 : ℝ) ^ n * Real.exp (-C * (n : ℝ) ^ a) ≤ ε := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hg := power_gap (a := 1) (b := a) (c := 2 * Real.log 2 / C) ha (by positivity)
  have ht := (power_exp_neg_tendsto (a := a) (c := C / 2) b
    (by linarith) (by positivity)).const_mul D
  have ht0 : Tendsto (fun n : ℕ => D * ((n : ℝ) ^ b * Real.exp (-(C / 2) * (n : ℝ) ^ a))) atTop (nhds 0) := by
    simpa only [mul_zero] using ht
  have hs := ht0.eventually (Iio_mem_nhds hε)
  filter_upwards [hg, hs] with n hg hs
  rw [Real.rpow_one] at hg
  have hn : (n : ℝ) * Real.log 2 ≤ (C / 2) * (n : ℝ) ^ a := by
    have hm := mul_lt_mul_of_pos_left hg (by positivity : 0 < C / 2)
    have he : (C / 2) * (2 * Real.log 2 / C * (n : ℝ)) = (n : ℝ) * Real.log 2 := by
      field_simp [hC.ne']
    rw [he] at hm
    exact hm.le
  have hp : (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  calc
    D * (n : ℝ) ^ b * (2 : ℝ) ^ n * Real.exp (-C * (n : ℝ) ^ a) =
        D * (n : ℝ) ^ b * Real.exp ((n : ℝ) * Real.log 2 - C * (n : ℝ) ^ a) := by
      rw [hp]
      have he : Real.exp ((n : ℝ) * Real.log 2) * Real.exp (-C * (n : ℝ) ^ a) =
          Real.exp ((n : ℝ) * Real.log 2 - C * (n : ℝ) ^ a) := by
        rw [← Real.exp_add]
        congr 1
        ring
      simpa only [mul_assoc] using congrArg (fun x => D * (n : ℝ) ^ b * x) he
    _ ≤ D * (n : ℝ) ^ b * Real.exp (-(C / 2) * (n : ℝ) ^ a) := by
      apply mul_le_mul_of_nonneg_left
      · apply Real.exp_le_exp.mpr
        linarith
      · exact mul_nonneg hD.le (Real.rpow_nonneg (Nat.cast_nonneg n) b)
    _ ≤ ε := by simpa only [mul_assoc] using hs.le

/-- The candidate polynomial bound gives a uniform logarithmic enumeration cost. -/
theorem candidate_log_bound (n C : ℕ) (hn : 2 ≤ n)
    (hC : (C : ℝ) ≤ 36 * (n : ℝ) ^ 16) :
    Real.log ((C : ℝ) + 1) ≤ 128 * Real.log (n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ 16 := one_le_pow₀ hn1
  have hbase : (C : ℝ) + 1 ≤ 37 * (n : ℝ) ^ 16 := by linarith
  have h37 : Real.log 37 ≤ 36 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 37)
    linarith
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
    rw [Real.log_inv] at h
    norm_num at h
    linarith
  have hlog : (1 / 2 : ℝ) ≤ Real.log (n : ℝ) :=
    h2.trans (Real.log_le_log (by norm_num) hn2)
  calc
    Real.log ((C : ℝ) + 1) ≤ Real.log (37 * (n : ℝ) ^ 16) :=
      Real.log_le_log (by positivity) hbase
    _ = Real.log 37 + 16 * Real.log (n : ℝ) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      norm_num
    _ ≤ 128 * Real.log (n : ℝ) := by linarith

end HypercubeRamsey.Lane_sol_s10_d2
