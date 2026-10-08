import HypercubeRamsey.S05.History_sol_s05_h3_patterns

namespace HypercubeRamsey.Lane_sol_s05_h23

open Classical Filter OAI.HypercubeRamsey Lane_q_s05_h23
open Lane_sol_s05_hist1b Lane_sol_s05_h5l
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {γ K' χ : ℝ}

 theorem T_le_J_eventually (p : Params5 γ K' χ) : ∀ᶠ n : ℕ in atTop, p.T n ≤ p.J n := by
  filter_upwards [(tendsto_m_atTop_h23 p).eventually_ge_atTop 1,
    fixed_power_margin p 2 (1 / 1000) (1 / 20) (by norm_num)] with n hm hpow
  change p.T n ≤ Nat.floor ((p.m n : ℝ) ^ (1 / 20 : ℝ))
  exact Nat.le_floor ((T_upper p n hm).trans hpow)

 theorem J_pos_of_m (p : Params5 γ K' χ) (n : ℕ) (hm : 1 ≤ p.m n) : 1 ≤ p.J n := by
  change 1 ≤ Nat.floor ((p.m n : ℝ) ^ (1 / 20 : ℝ))
  apply Nat.le_floor
  have hmr : (1 : ℝ) ≤ (p.m n : ℝ) := by exact_mod_cast hm
  have hh : (1 : ℝ) ≤ (p.m n : ℝ) ^ (1 / 20 : ℝ) := Real.one_le_rpow hmr (by norm_num)
  simpa only [Nat.cast_one] using hh

private theorem real_power_exp (x : ℝ) (hx : 0 < x) (k : ℕ) :
    x ^ k = Real.exp ((k : ℝ) * Real.log x) := by
  calc
    _ = (Real.exp (Real.log x)) ^ k := by rw [Real.exp_log hx]
    _ = _ := by rw [← Real.exp_nat_mul]

 theorem highRecordCountBound_exp (p : Params5 γ K' χ) (n : ℕ)
    (hm : 2 ≤ p.m n) (hT : p.T n ≤ p.J n) (hJ : 1 ≤ p.J n) :
    (highRecordCountBound p n : ℝ) ≤
      Real.exp (((signatureConstant : ℝ) + 200) * (p.J n : ℝ) * Real.log (p.m n : ℝ)) := by
  have hmr : (2 : ℝ) ≤ p.m n := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < p.m n := by linarith
  have hTr : (p.T n : ℝ) ≤ p.J n := by exact_mod_cast hT
  have hJr : (1 : ℝ) ≤ p.J n := by exact_mod_cast hJ
  have hD : (0 : ℝ) ≤ signatureConstant := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log (p.m n : ℝ) := Real.log_nonneg (by linarith)
  have hlog2 : Real.log 2 ≤ Real.log (p.m n : ℝ) := Real.log_le_log (by norm_num) hmr
  have hlogp : Real.log ((p.m n : ℝ) + 1) ≤ 2 * Real.log (p.m n : ℝ) := by
    apply (Real.log_le_log (by positivity) (show (p.m n : ℝ) + 1 ≤ (p.m n : ℝ) ^ 2 by nlinarith)).trans
    rw [Real.log_pow]
    norm_num
  have hgen : (p.T n : ℝ) * signatureConstant * Real.log 2 ≤
      (p.J n : ℝ) * signatureConstant * Real.log (p.m n : ℝ) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_right hTr hD) hlog2
      (Real.log_pos (by norm_num)).le (mul_nonneg (Nat.cast_nonneg _) hD)
  have hpoly := mul_le_mul_of_nonneg_left hlogp
    (show (0 : ℝ) ≤ 20 * ((p.J n : ℝ) + 4) by positivity)
  have hcoef : 20 * ((p.J n : ℝ) + 4) * 2 ≤ 200 * (p.J n : ℝ) := by linarith
  have hpoly' := mul_le_mul_of_nonneg_right hcoef hlog
  unfold highRecordCountBound
  push_cast
  rw [real_power_exp 2 (by norm_num), real_power_exp _ (by positivity), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  push_cast
  nlinarith [hgen, hpoly, hpoly']

 theorem highRecordBudget_le (p : Params5 γ K' χ) (n : ℕ) (cH : ℝ)
    (hcH : 0 < cH) (hKs : 2 * ((signatureConstant : ℝ) + 204) / cH ≤ p.Ks)
    (hm : 2 ≤ p.m n) (hT : p.T n ≤ p.J n) (hJ : 1 ≤ p.J n) :
    (3 * highRecordCountBound p n : ℕ) * Real.exp (-(cH * p.s n) / 2) ≤
      3 * Real.exp (-4 * Real.log (p.m n : ℝ)) := by
  have hb := highRecordCountBound_exp p n hm hT hJ
  have hlog : 0 ≤ Real.log (p.m n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ p.m n by omega))
  have hL : 0 ≤ (p.J n : ℝ) * Real.log (p.m n : ℝ) := mul_nonneg (Nat.cast_nonneg _) hlog
  have hK : 2 * ((signatureConstant : ℝ) + 204) ≤ cH * p.Ks := by
    have h := (div_le_iff₀ hcH).mp hKs
    nlinarith
  have hs : p.Ks * (p.J n : ℝ) * Real.log (p.m n : ℝ) ≤ (p.s n : ℝ) := Nat.le_ceil _
  have hmain : 2 * ((signatureConstant : ℝ) + 204) *
      ((p.J n : ℝ) * Real.log (p.m n : ℝ)) ≤ cH * (p.s n : ℝ) := by
    calc
      _ ≤ (cH * p.Ks) * ((p.J n : ℝ) * Real.log (p.m n : ℝ)) := mul_le_mul_of_nonneg_right hK hL
      _ = cH * (p.Ks * (p.J n : ℝ) * Real.log (p.m n : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs hcH.le
  have hJL : Real.log (p.m n : ℝ) ≤ (p.J n : ℝ) * Real.log (p.m n : ℝ) :=
    le_mul_of_one_le_left hlog (by exact_mod_cast hJ)
  push_cast
  calc
    _ ≤ (3 * Real.exp (((signatureConstant : ℝ) + 200) * (p.J n : ℝ) * Real.log (p.m n : ℝ))) *
        Real.exp (-(cH * p.s n) / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num)) (Real.exp_pos _).le
    _ = 3 * Real.exp ((((signatureConstant : ℝ) + 200) * (p.J n : ℝ) * Real.log (p.m n : ℝ)) -
        (cH * p.s n) / 2) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num : (0 : ℝ) ≤ 3)
      nlinarith [hmain, hJL]

 def highGroupBudget (p : Params5 γ K' χ) (n : ℕ) : ℝ :=
  stage2GroupBudgetVanishing5 (halfDelta p) n + 3 * Real.exp (-4 * Real.log (p.m n : ℝ))

 theorem highGroupBudget_tendsto (p : Params5 γ K' χ) :
    Tendsto (highGroupBudget p) atTop (𝓝 0) := by
  have hl := Real.tendsto_log_atTop.comp (tendsto_m_atTop_h23 p)
  have he : Tendsto (fun n => Real.exp (-4 * Real.log (p.m n : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (hl.const_mul_atTop (by norm_num : (0 : ℝ) < 4))
  change Tendsto (fun n => stage2GroupBudgetVanishing5 (halfDelta p) n +
    3 * Real.exp (-4 * Real.log (p.m n : ℝ))) atTop (𝓝 0)
  simpa only [mul_zero, add_zero] using
    (stage3PatternBudget_tendsto p).add (he.const_mul 3)

 theorem highGroupBudget_nonneg (p : Params5 γ K' χ) (n : ℕ) : 0 ≤ highGroupBudget p n :=
  add_nonneg (stage2Budget_nonneg (halfDelta p) n) (by positivity)

 theorem highGroupBounds_eventually (p : Params5 γ K' χ) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ p.m n ∧ signatureConstant ≤ p.m n ∧
      p.T n ≤ p.m n ∧ p.T n ≤ p.J n ∧ 1 ≤ p.J n ∧
      highGroupBudget p n < 1 / 2 ∧ (coarseCountBound 4 : ℝ) * highGroupBudget p n ≤ 1 / 4 := by
  have ht := highGroupBudget_tendsto p
  filter_upwards [record_count_budgets_eventually p, T_le_J_eventually p,
    ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2),
    (ht.const_mul (coarseCountBound 4 : ℝ)).eventually_lt_const
      (by simp only [mul_zero]; norm_num : (coarseCountBound 4 : ℝ) * 0 < 1 / 4)]
    with n hd hTJ hb hn
  obtain ⟨hm, hD, hTlo, hT, hpool⟩ := hd
  exact ⟨hm, hD, hT, hTJ, J_pos_of_m p n (by omega), hb, hn.le⟩

end
end HypercubeRamsey.Lane_sol_s05_h23
