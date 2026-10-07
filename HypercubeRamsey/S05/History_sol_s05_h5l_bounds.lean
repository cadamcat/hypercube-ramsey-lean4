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

theorem fixed_power_margin (p : Params5 γ K' χ) (A a b : ℝ) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, A * (p.m n : ℝ) ^ a ≤ (p.m n : ℝ) ^ b := by
  have hm := Lane_sol_s05_h1.tendsto_m p
  have hmargin : Tendsto (fun n => (p.m n : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).comp hm
  filter_upwards [hm.eventually_ge_atTop 1, hmargin.eventually_ge_atTop A] with n hn hA
  have hp : (0 : ℝ) < p.m n := lt_of_lt_of_le (by norm_num) hn
  have hh := mul_le_mul_of_nonneg_left hA (Real.rpow_nonneg hp.le a)
  have he : (p.m n : ℝ) ^ a * (p.m n : ℝ) ^ (b - a) = (p.m n : ℝ) ^ b := by
    rw [← Real.rpow_add hp]
    congr 1
    ring
  simpa only [he, mul_comm] using hh

theorem uStarSeg_positive (p : Params5 γ K' χ) (n : ℕ) (hm : 1 < p.m n) :
    0 < p.uStarSeg n := by
  have hlog : 0 < Real.log (p.m n : ℝ) := Real.log_pos (by exact_mod_cast hm)
  have hq : (0 : ℝ) < p.q0 := by exact_mod_cast p.hq0.1
  have hraw : 0 < p.eta * Real.log (p.m n : ℝ) / p.q0 :=
    div_pos (mul_pos p.heta.1 hlog) hq
  have hle : p.eta * Real.log (p.m n : ℝ) / p.q0 ≤ (p.uStarSeg n : ℝ) := Nat.le_ceil _
  exact_mod_cast hraw.trans_le hle

theorem used_length_upper (p : Params5 γ K' χ) (n : ℕ) (hm : 1 < p.m n) :
    (p.q0 * p.uStarSeg n * p.usedBlocks n : ℕ) ≤
      (p.m n : ℝ) ^ (1 / 200 : ℝ) + (p.q0 : ℝ) * p.uStarSeg n := by
  have hq : (0 : ℝ) < p.q0 := by exact_mod_cast p.hq0.1
  have hu : (0 : ℝ) < p.uStarSeg n := by exact_mod_cast uStarSeg_positive p n hm
  have hd : 0 < (p.q0 : ℝ) * p.uStarSeg n := mul_pos hq hu
  have hceil := Nat.ceil_lt_add_one (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (p.m n)) (1 / 200 : ℝ)) hd.le)
  change (p.usedBlocks n : ℝ) < (p.m n : ℝ) ^ (1 / 200 : ℝ) /
    ((p.q0 : ℝ) * p.uStarSeg n) + 1 at hceil
  have hh := mul_le_mul_of_nonneg_left hceil.le hd.le
  rw [mul_add, mul_div_cancel₀ _ hd.ne', mul_one] at hh
  simpa only [Nat.cast_mul] using hh

theorem T_upper (p : Params5 γ K' χ) (n : ℕ) (hm : 1 ≤ (p.m n : ℝ)) :
    (p.T n : ℝ) ≤ 2 * (p.m n : ℝ) ^ (1 / 1000 : ℝ) := by
  have hpow : 1 ≤ (p.m n : ℝ) ^ (1 / 1000 : ℝ) := Real.one_le_rpow hm (by norm_num)
  have hh := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg (p.m n)) (1 / 1000 : ℝ))
  change (p.T n : ℝ) < (p.m n : ℝ) ^ (1 / 1000 : ℝ) + 1 at hh
  linarith

theorem T_log_upper (p : Params5 γ K' χ) (n : ℕ) (hm : 1 ≤ (p.m n : ℝ)) :
    (p.T n : ℝ) * Real.log (p.T n) ≤ 4 * (p.m n : ℝ) ^ (1 / 500 : ℝ) := by
  have hT := T_upper p n hm
  have hTp : (0 : ℝ) < p.T n := by
    have hh : (p.m n : ℝ) ^ (1 / 1000 : ℝ) ≤ (p.T n : ℝ) := Nat.le_ceil _
    exact (Real.rpow_pos_of_pos (lt_of_lt_of_le (by norm_num) hm) _).trans_le hh
  have hlog := (Real.log_le_sub_one_of_pos hTp).trans (by linarith : (p.T n : ℝ) - 1 ≤ p.T n)
  have hsq : ((p.T n : ℝ)) ^ 2 ≤ (2 * (p.m n : ℝ) ^ (1 / 1000 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hTp.le hT 2
  have he : ((p.m n : ℝ) ^ (1 / 1000 : ℝ)) ^ 2 = (p.m n : ℝ) ^ (1 / 500 : ℝ) := by
    rw [pow_two, ← Real.rpow_add (lt_of_lt_of_le (by norm_num) hm)]
    norm_num
  have hh := mul_le_mul_of_nonneg_left hlog hTp.le
  rw [← pow_two] at hh
  calc
    _ ≤ (p.T n : ℝ) ^ 2 := hh
    _ ≤ (2 * (p.m n : ℝ) ^ (1 / 1000 : ℝ)) ^ 2 := hsq
    _ = _ := by rw [mul_pow, he]; norm_num

/-- The interface-mask count is uniformly negligible compared with the low power margin. -/
theorem low_pattern_overhead_eventually (p : Params5 γ K' χ) :
    ∀ᶠ n : ℕ in atTop,
      (p.T n : ℝ) * Real.log (p.T n) +
        (p.T n : ℝ) * (p.q0 * p.uStarSeg n * p.usedBlocks n : ℕ) ≤
          (p.m n : ℝ) ^ (1 / 50 : ℝ) := by
  let P : ℝ := 1 + 1000 * p.eta + p.q0
  have hm := Lane_sol_s05_h1.tendsto_m p
  filter_upwards [hm.eventually_ge_atTop 2,
    fixed_power_margin p (4 + 2 * P) (3 / 500) (1 / 50) (by norm_num)] with n hn hmargin
  have hM : (1 : ℝ) ≤ p.m n := by linarith
  have hmnat : 1 < p.m n := by exact_mod_cast (show (1 : ℝ) < p.m n by linarith)
  have hlog : Real.log (p.m n : ℝ) ≤ 1000 * (p.m n : ℝ) ^ (1 / 1000 : ℝ) := by
    have hh := Real.log_le_rpow_div (Nat.cast_nonneg (p.m n)) (by norm_num : (0 : ℝ) < 1 / 1000)
    convert hh using 1 <;> ring
  have hU : (p.q0 : ℝ) * p.uStarSeg n ≤ p.eta * Real.log (p.m n : ℝ) + p.q0 := by
    have hq : (0 : ℝ) < p.q0 := by exact_mod_cast p.hq0.1
    have hh := Nat.ceil_lt_add_one (div_nonneg
      (mul_nonneg p.heta.1.le (Real.log_nonneg hM)) hq.le)
    change (p.uStarSeg n : ℝ) < p.eta * Real.log (p.m n : ℝ) / p.q0 + 1 at hh
    have hmul := mul_le_mul_of_nonneg_left hh.le hq.le
    rw [mul_add, mul_div_cancel₀ _ hq.ne', mul_one] at hmul
    exact hmul
  have hsmall : (p.m n : ℝ) ^ (1 / 1000 : ℝ) ≤ (p.m n : ℝ) ^ (1 / 200 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hM (by norm_num)
  have hpow1 : 1 ≤ (p.m n : ℝ) ^ (1 / 200 : ℝ) := Real.one_le_rpow hM (by norm_num)
  have hU' : (p.q0 : ℝ) * p.uStarSeg n ≤ (1000 * p.eta + p.q0) * (p.m n : ℝ) ^ (1 / 200 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (hlog.trans (mul_le_mul_of_nonneg_left hsmall (by norm_num))) p.heta.1.le
    have hq := mul_le_mul_of_nonneg_left hpow1 (Nat.cast_nonneg p.q0)
    nlinarith [hU]
  have hk : (p.q0 * p.uStarSeg n * p.usedBlocks n : ℕ) ≤ P * (p.m n : ℝ) ^ (1 / 200 : ℝ) := by
    have hh := used_length_upper p n hmnat
    dsimp only [P]
    linarith
  have ht := T_upper p n hM
  have hprod := mul_le_mul ht hk (Nat.cast_nonneg _) (by positivity : 0 ≤ 2 * (p.m n : ℝ) ^ (1 / 1000 : ℝ))
  have he : (p.m n : ℝ) ^ (1 / 1000 : ℝ) * (p.m n : ℝ) ^ (1 / 200 : ℝ) =
      (p.m n : ℝ) ^ (3 / 500 : ℝ) := by
    rw [← Real.rpow_add (lt_of_lt_of_le (by norm_num) hM)]
    norm_num
  have hprod' : (p.T n : ℝ) * (p.q0 * p.uStarSeg n * p.usedBlocks n : ℕ) ≤
      2 * P * (p.m n : ℝ) ^ (3 / 500 : ℝ) := by
    convert hprod using 1
    rw [show 2 * (p.m n : ℝ) ^ (1 / 1000 : ℝ) * (P * (p.m n : ℝ) ^ (1 / 200 : ℝ)) =
      2 * P * ((p.m n : ℝ) ^ (1 / 1000 : ℝ) * (p.m n : ℝ) ^ (1 / 200 : ℝ)) by ring, he]
  have htlog := T_log_upper p n hM
  have hp := Real.rpow_le_rpow_of_exponent_le hM (by norm_num : (1 / 500 : ℝ) ≤ 3 / 500)
  have htlog' := htlog.trans (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 4))
  have hsum := add_le_add htlog' hprod'
  have hh : (p.T n : ℝ) * Real.log (p.T n) +
      (p.T n : ℝ) * (p.q0 * p.uStarSeg n * p.usedBlocks n : ℕ) ≤
        (4 + 2 * P) * (p.m n : ℝ) ^ (3 / 500 : ℝ) := by
    convert hsum using 1 <;> ring
  exact hh.trans hmargin

theorem high_pattern_overhead_eventually (p : Params5 γ K' χ) :
    ∀ᶠ n : ℕ in atTop,
      (p.T n : ℝ) * Real.log (p.T n) ≤ (p.J n : ℝ) * Real.log (p.m n) := by
  have hm := Lane_sol_s05_h1.tendsto_m p
  have hp : Tendsto (fun n => (p.m n : ℝ) ^ (1 / 20 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp hm
  filter_upwards [hm.eventually_ge_atTop 1, hp.eventually_ge_atTop 2,
    (Real.tendsto_log_atTop.comp hm).eventually_ge_atTop 1,
    fixed_power_margin p 8 (1 / 500) (1 / 20) (by norm_num)] with n hM hpow hlog hmargin
  dsimp only [Function.comp_apply] at hlog
  have hfloor : (p.m n : ℝ) ^ (1 / 20 : ℝ) < (p.J n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hJ : (p.m n : ℝ) ^ (1 / 20 : ℝ) / 2 ≤ p.J n := by linarith
  have ht := T_log_upper p n hM
  have hJl := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (p.J n))
  nlinarith

end
end HypercubeRamsey.Lane_sol_s05_h5l
