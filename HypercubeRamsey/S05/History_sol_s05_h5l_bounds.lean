import HypercubeRamsey.S05.Bounds_sol_s05_h1

namespace HypercubeRamsey.Lane_sol_s05_h5l

open Classical Filter
open scoped Topology

noncomputable section
set_option maxHeartbeats 800000

variable {γ K' χ : ℝ}

theorem uSeg_positive (p : Params5 γ K' χ) (n j : ℕ) (hm : 1 < p.m n) :
    0 < p.uSeg n j := by
  have hlog : 0 < Real.log (p.m n : ℝ) := Real.log_pos (by exact_mod_cast hm)
  have hq : (0 : ℝ) < p.q0 := by exact_mod_cast p.hq0.1
  have hraw : 0 < p.K1 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ) / p.q0 :=
    div_pos (mul_pos (mul_pos p.hK1 (by positivity)) hlog) hq
  have hle : p.K1 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ) / p.q0 ≤ (p.uSeg n j : ℝ) := Nat.le_ceil _
  exact_mod_cast hraw.trans_le hle

theorem low_length_lower (p : Params5 γ K' χ) (n j : ℕ) (hm : 1 < p.m n) :
    p.K2 * (((j : ℝ) + 4) * Real.log (p.m n : ℝ) + (p.m n : ℝ) ^ (1 / 50 : ℝ)) ≤
      (p.q0 * p.uSeg n j * p.lowBlocks n j : ℕ) := by
  have hq : (0 : ℝ) < p.q0 := by exact_mod_cast p.hq0.1
  have hu : (0 : ℝ) < p.uSeg n j := by exact_mod_cast uSeg_positive p n j hm
  have hden : 0 < (p.q0 : ℝ) * p.uSeg n j := mul_pos hq hu
  have hh : p.K2 * (((j : ℝ) + 4) * Real.log (p.m n : ℝ) + (p.m n : ℝ) ^ (1 / 50 : ℝ)) /
      ((p.q0 : ℝ) * p.uSeg n j) ≤ (p.lowBlocks n j : ℝ) := Nat.le_ceil _
  have hh' := (div_le_iff₀ hden).1 hh
  push_cast
  nlinarith

/-- The neighbouring severity lengths retain a uniform logarithmic and power margin. -/
theorem kPrime_lower (p : Params5 γ K' χ) (n j : ℕ) (hm : 1 < p.m n) :
    p.K2 * (((j : ℝ) + 3) * Real.log (p.m n : ℝ) + (p.m n : ℝ) ^ (1 / 50 : ℝ)) ≤
      (p.kPrime n j : ℝ) := by
  have hlog : 0 ≤ Real.log (p.m n : ℝ) := (Real.log_pos (by exact_mod_cast hm)).le
  have hlo (j' : ℕ) (hlevel : (j : ℝ) + 3 ≤ (j' : ℝ) + 4) :
      p.K2 * (((j : ℝ) + 3) * Real.log (p.m n : ℝ) + (p.m n : ℝ) ^ (1 / 50 : ℝ)) ≤
        (p.q0 * p.uSeg n j' * p.lowBlocks n j' : ℕ) := by
    refine le_trans ?_ (low_length_lower p n j' hm)
    apply mul_le_mul_of_nonneg_left _ p.hK2.le
    gcongr
  unfold Params5.kPrime
  push_cast
  apply le_min
  · apply le_min
    · simpa only [Nat.cast_mul] using hlo j (by linarith)
    · simpa only [Nat.cast_mul] using hlo (j + 1) (by push_cast; linarith)
  · simpa only [Nat.cast_mul] using hlo (j - 1)
      (by exact_mod_cast (show j + 3 ≤ (j - 1) + 4 by omega))

theorem pow_two_exp_loss (d : ℕ) (c s : ℝ)
    (hbudget : (d : ℝ) * Real.log 2 ≤ c * s / 12) :
    (2 : ℝ) ^ d * Real.exp (-(c * s) / 3) ≤ Real.exp (-(c * s) / 4) := by
  have hpow : (2 : ℝ) ^ d = Real.exp ((d : ℝ) * Real.log 2) := by
    calc
      (2 : ℝ) ^ d = (Real.exp (Real.log 2)) ^ d := by rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = _ := by rw [← Real.exp_nat_mul]
  rw [hpow, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- A fixed `O(J)` coordinate loss is negligible compared with the high history length. -/
theorem high_scope_budget_eventually (p : Params5 γ K' χ) (D c : ℝ)
    (hD : 0 ≤ D) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, D * ((p.J n : ℝ) + 4) * Real.log 2 ≤ c * (p.s n : ℝ) / 12 := by
  have hm := Lane_sol_s05_h1.tendsto_m p
  have hpow : Tendsto (fun n => (p.m n : ℝ) ^ (1 / 20 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp hm
  have hJ : ∀ᶠ n : ℕ in atTop, (4 : ℝ) ≤ p.J n := by
    filter_upwards [hpow.eventually_ge_atTop 5] with n hn
    have hh : (p.m n : ℝ) ^ (1 / 20 : ℝ) < (p.J n : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hlog := Real.tendsto_log_atTop.comp hm
  have hthreshold : ∀ᶠ n : ℕ in atTop,
      24 * D * Real.log 2 / (c * p.Ks) ≤ Real.log (p.m n : ℝ) :=
    hlog.eventually_ge_atTop _
  filter_upwards [hJ, hthreshold] with n hJn hln
  have hcoef : 0 < c * p.Ks := mul_pos hc p.hKs
  have hlogn : 24 * D * Real.log 2 ≤ c * p.Ks * Real.log (p.m n : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hcoef).1 hln
  have hs : p.Ks * (p.J n : ℝ) * Real.log (p.m n : ℝ) ≤ (p.s n : ℝ) := Nat.le_ceil _
  have hJ0 : 0 ≤ (p.J n : ℝ) := Nat.cast_nonneg _
  have hcoeff : 0 ≤ D * Real.log 2 := mul_nonneg hD (Real.log_pos (by norm_num)).le
  have hmul := mul_le_mul_of_nonneg_right hlogn hJ0
  have hsl := mul_le_mul_of_nonneg_left hs hc.le
  nlinarith

end
end HypercubeRamsey.Lane_sol_s05_h5l
