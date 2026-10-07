import HypercubeRamsey.S09.Defs

open Filter

namespace HypercubeRamsey.Lane_q_s09_misc

/-- A fixed multiple of a lower power is eventually below any strictly higher power. -/
theorem eventually_nat_rpow_const_mul_le {a b c : ℝ} (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ a ≤ (n : ℝ) ^ b := by
  have hgap : 0 < b - a := sub_pos.mpr hab
  have hpow : ∀ᶠ n : ℕ in atTop, c ≤ (n : ℝ) ^ (b - a) := by
    have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (b - a)) atTop atTop :=
      (tendsto_rpow_atTop hgap).comp tendsto_natCast_atTop_atTop
    exact ht.eventually (eventually_ge_atTop c)
  filter_upwards [hpow, eventually_ge_atTop (1 : ℕ)] with n hcn hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hna : 0 ≤ (n : ℝ) ^ a := le_of_lt (Real.rpow_pos_of_pos hnR a)
  calc
    c * (n : ℝ) ^ a ≤ (n : ℝ) ^ (b - a) * (n : ℝ) ^ a :=
      mul_le_mul_of_nonneg_right hcn hna
    _ = (n : ℝ) ^ b := by
      rw [← Real.rpow_add hnR]
      congr 1
      ring

/-- The standard logarithmic bound, arranged for dimensions cast from naturals. -/
theorem eventually_nat_log_le_rpow_div {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ (n : ℝ) ^ δ / δ := by
  filter_upwards with n
  exact Real.log_natCast_le_rpow_div n hδ

/-- A logarithm at `n+1` is bounded by a small power of `n`, for `0 < δ ≤ 1`. -/
theorem eventually_nat_log_succ_le_rpow {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᶠ n : ℕ in atTop, Real.log ((n : ℝ) + 1) ≤ (2 / δ) * (n : ℝ) ^ δ := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnp : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
  have hlog := Real.log_natCast_le_rpow_div (n + 1) hδ
  have hlog' : Real.log ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ δ / δ := by
    simpa only [Nat.cast_add, Nat.cast_one] using hlog
  have hbase : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by nlinarith
  have hpow : ((n : ℝ) + 1) ^ δ ≤ (2 * (n : ℝ)) ^ δ :=
    Real.rpow_le_rpow (by positivity) hbase hδ.le
  have hmul : (2 * (n : ℝ)) ^ δ = (2 : ℝ) ^ δ * (n : ℝ) ^ δ :=
    Real.mul_rpow (by norm_num) hnp.le
  have h2 : (2 : ℝ) ^ δ ≤ 2 := by
    calc
      (2 : ℝ) ^ δ ≤ 2 ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hδ1
      _ = 2 := by norm_num
  calc
    Real.log ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ δ / δ := hlog'
    _ ≤ (2 * (n : ℝ)) ^ δ / δ := by gcongr
    _ = (2 : ℝ) ^ δ * (n : ℝ) ^ δ / δ := by rw [hmul]
    _ ≤ 2 * (n : ℝ) ^ δ / δ := by gcongr
    _ = (2 / δ) * (n : ℝ) ^ δ := by ring

/-- Cast a rational strict inequality to the reals without normalizing its rational syntax. -/
theorem ratCast_lt {a b : ℚ} (h : a < b) : (a : ℝ) < (b : ℝ) := by
  exact_mod_cast h

/-- Cast a rational weak inequality to the reals without normalizing its rational syntax. -/
theorem ratCast_le {a b : ℚ} (h : a ≤ b) : (a : ℝ) ≤ (b : ℝ) := by
  exact_mod_cast h

end HypercubeRamsey.Lane_q_s09_misc
