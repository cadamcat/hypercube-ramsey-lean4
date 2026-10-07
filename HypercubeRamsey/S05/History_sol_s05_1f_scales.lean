import HypercubeRamsey.S05.History_sol_s05_1f
import HypercubeRamsey.S05.History_sol_s05_h5l_bounds

namespace HypercubeRamsey.Lane_sol_s05_1f

open Classical Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {γ K' χ : ℝ}

/-- The full pool grows below `m^0.03`, as required by `heta`. -/
theorem poolBlocks_power_upper (p : Params5 γ K' χ) (n : ℕ) (hm : 1 < p.m n) :
    (p.poolBlocks n : ℝ) ≤
      (2 * Real.exp (p.Kh * p.q0) + 1) * (p.m n : ℝ) ^ (3 / 100 : ℝ) := by
  let M : ℝ := p.m n
  have hM : 1 ≤ M := by dsimp only [M]; exact_mod_cast (Nat.le_of_lt hm)
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hlog : 0 ≤ Real.log M := Real.log_nonneg hM
  have hq : (0 : ℝ) < p.q0 := by exact_mod_cast p.hq0.1
  have hu : 0 < p.uStarSeg n := Lane_sol_s05_h5l.uStarSeg_positive p n hm
  have hden : (1 : ℝ) ≤ (p.q0 : ℝ) * p.uStarSeg n := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.mul_pos p.hq0.1 hu))
  have hU : (p.q0 : ℝ) * p.uStarSeg n ≤ p.eta * Real.log M + p.q0 := by
    have hh := Nat.ceil_lt_add_one (div_nonneg (mul_nonneg p.heta.1.le hlog) hq.le)
    change (p.uStarSeg n : ℝ) < p.eta * Real.log M / p.q0 + 1 at hh
    have hh' := mul_le_mul_of_nonneg_left hh.le hq.le
    rw [mul_add, mul_div_cancel₀ _ hq.ne', mul_one] at hh'
    exact hh'
  have hpower : 1 ≤ M ^ (1 / 200 : ℝ) := Real.one_le_rpow hM (by norm_num)
  have hused : (p.usedBlocks n : ℝ) ≤ 2 * M ^ (1 / 200 : ℝ) := by
    have hh := Nat.ceil_lt_add_one (div_nonneg (Real.rpow_nonneg hMpos.le (1 / 200 : ℝ)) (by linarith :
      0 ≤ (p.q0 : ℝ) * p.uStarSeg n))
    change (p.usedBlocks n : ℝ) < M ^ (1 / 200 : ℝ) /
      ((p.q0 : ℝ) * p.uStarSeg n) + 1 at hh
    have hdiv : M ^ (1 / 200 : ℝ) / ((p.q0 : ℝ) * p.uStarSeg n) ≤ M ^ (1 / 200 : ℝ) := by
      apply (div_le_iff₀ (by linarith : 0 < (p.q0 : ℝ) * p.uStarSeg n)).mpr
      exact le_mul_of_one_le_right (Real.rpow_nonneg hMpos.le _) hden
    linarith
  let C := Real.exp (p.Kh * p.q0)
  have hExp : Real.exp (p.Kh * ((p.q0 : ℝ) * p.uStarSeg n)) ≤ C * M ^ (p.Kh * p.eta) := by
    apply le_trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hU p.hKh.le))
    apply le_of_eq
    dsimp only [C]
    rw [Real.rpow_def_of_pos hMpos, ← Real.exp_add]
    congr 1
    ring
  have hceil := Nat.ceil_lt_add_one (mul_nonneg
    (Real.exp_pos (p.Kh * ((p.q0 : ℝ) * p.uStarSeg n))).le
    (Nat.cast_nonneg (p.usedBlocks n)))
  change (p.poolBlocks n : ℝ) <
    Real.exp (p.Kh * ((p.q0 : ℝ) * p.uStarSeg n)) * p.usedBlocks n + 1 at hceil
  have hprod := mul_le_mul hExp hused (Nat.cast_nonneg (p.usedBlocks n))
    (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hMpos.le _))
  have he : (C * M ^ (p.Kh * p.eta)) * (2 * M ^ (1 / 200 : ℝ)) =
      2 * C * M ^ (p.Kh * p.eta + 1 / 200) := by
    rw [Real.rpow_add hMpos]
    ring
  rw [he] at hprod
  have hp : M ^ (p.Kh * p.eta + 1 / 200) ≤ M ^ (3 / 100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hM p.heta.2.le
  have hp1 : 1 ≤ M ^ (3 / 100 : ℝ) := Real.one_le_rpow hM (by norm_num)
  have hprod' := hprod.trans (mul_le_mul_of_nonneg_left hp (by dsimp [C]; positivity))
  change (p.poolBlocks n : ℝ) ≤ (2 * C + 1) * M ^ (3 / 100 : ℝ)
  nlinarith

theorem high_history_power_lower (p : Params5 γ K' χ) :
    ∀ᶠ n : ℕ in atTop, p.Ks * (p.m n : ℝ) ^ (1 / 20 : ℝ) / 2 ≤ (p.s n : ℝ) := by
  have hm := Lane_sol_s05_h1.tendsto_m p
  have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp hm
  filter_upwards [hpow.eventually_ge_atTop 2,
    (Real.tendsto_log_atTop.comp hm).eventually_ge_atTop 1] with n hp hl
  dsimp only [Function.comp_apply] at hl hp
  have hfloor : (p.m n : ℝ) ^ (1 / 20 : ℝ) < (p.J n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hJ : (p.m n : ℝ) ^ (1 / 20 : ℝ) / 2 ≤ p.J n := by linarith
  have hs : p.Ks * (p.J n : ℝ) * Real.log (p.m n : ℝ) ≤ p.s n := Nat.le_ceil _
  have hmul := mul_le_mul_of_nonneg_left hJ p.hKs.le
  have hlog := mul_le_mul_of_nonneg_left hl
    (mul_nonneg p.hKs.le (Nat.cast_nonneg (p.J n)))
  nlinarith

/-- Both the dimension-size reference union and the pool-subset union fit
in the high denominator budget. No additional parameter request is needed. -/
theorem high_denominator_budget_eventually (p : Params5 γ K' χ) :
    ∀ᶠ n : ℕ in atTop,
      0 < n ∧ 1 ≤ p.usedBlocks n * (p.q0 * p.uStarSeg n) ∧
      Real.log (n : ℝ) + (p.poolBlocks n : ℝ) * Real.log 2 ≤ p.delta * p.s n / 2 ∧
      4 * Real.log 2 ≤ p.delta * p.s n := by
  let A := 8 * (2 * Real.exp (p.Kh * p.q0) + 1) * Real.log 2 / (p.delta * p.Ks)
  have hcoef : 0 < p.delta * p.Ks / 8 :=
    div_pos (mul_pos p.hdelta.1 p.hKs) (by norm_num)
  have hlogsmall := ((isLittleO_log_rpow_atTop (div_pos p.halpha.1 (by norm_num : (0 : ℝ) < 20))).comp_tendsto
    tendsto_natCast_atTop_atTop).bound hcoef
  have hm := Lane_sol_s05_h1.tendsto_m p
  have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp hm
  filter_upwards [hm.eventually_ge_atTop 2, high_history_power_lower p,
    Lane_sol_s05_h5l.fixed_power_margin p A (3 / 100) (1 / 20) (by norm_num),
    hlogsmall, hpow.eventually_ge_atTop (8 * Real.log 2 / (p.delta * p.Ks)),
    eventually_ge_atTop (2 : ℕ)] with n hM hs hmargin hlog hlarge hn
  have hmnat : 1 < p.m n := by exact_mod_cast (show (1 : ℝ) < p.m n by linarith)
  have hu : 0 < p.uStarSeg n := Lane_sol_s05_h5l.uStarSeg_positive p n hmnat
  have hden : 0 < p.q0 * p.uStarSeg n := Nat.mul_pos p.hq0.1 hu
  have hused : 0 < p.usedBlocks n := by
    have hd : (0 : ℝ) < (p.q0 : ℝ) * p.uStarSeg n := by exact_mod_cast hden
    have hp : (0 : ℝ) < (p.m n : ℝ) ^ (1 / 200 : ℝ) :=
      Real.rpow_pos_of_pos (by linarith) _
    have hh := (div_pos hp hd).trans_le (Nat.le_ceil
      ((p.m n : ℝ) ^ (1 / 200 : ℝ) / ((p.q0 : ℝ) * p.uStarSeg n)))
    exact Nat.cast_pos.mp hh
  refine ⟨by omega, Nat.succ_le_of_lt (Nat.mul_pos hused hden), ?_, ?_⟩
  · have hpool := poolBlocks_power_upper p n hmnat
    have hp := mul_le_mul_of_nonneg_right hpool (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    dsimp only [A] at hmargin
    rw [div_mul_eq_mul_div] at hmargin
    have hmargin' := (div_le_iff₀ (mul_pos p.hdelta.1 p.hKs)).mp hmargin
    have hpoolbudget : (p.poolBlocks n : ℝ) * Real.log 2 ≤ p.delta * (p.s n : ℝ) / 4 := by
      have hsl := mul_le_mul_of_nonneg_left hs p.hdelta.1.le
      nlinarith
    have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hnlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
    have hlog' : Real.log (n : ℝ) ≤ p.delta * p.Ks / 8 * (n : ℝ) ^ (p.alpha / 20) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hnlog,
        abs_of_nonneg (Real.rpow_nonneg hn0 _), Function.comp_apply] using hlog
    have hpowM : (n : ℝ) ^ (p.alpha / 20) ≤ (p.m n : ℝ) ^ (1 / 20 : ℝ) := by
      calc
        _ = ((n : ℝ) ^ p.alpha) ^ (1 / 20 : ℝ) := by
          rw [← Real.rpow_mul hn0]
          congr 1
          ring
        _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hn0 _) (Nat.le_ceil _) (by norm_num)
    have hh := mul_le_mul_of_nonneg_left hpowM hcoef.le
    have hsl := mul_le_mul_of_nonneg_left hs p.hdelta.1.le
    nlinarith
  · have hh := (div_le_iff₀ (mul_pos p.hdelta.1 p.hKs)).mp hlarge
    dsimp only [Function.comp_apply] at hh
    have hsl := mul_le_mul_of_nonneg_left hs p.hdelta.1.le
    nlinarith

/-- The complete high-target raw denominator estimate, with rate `δ/4`.
Only the additional high-row feasibility failures remain. -/
theorem high_denominator_eventual_bound (p : Params5 γ K' χ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (X : Setup5 γ K' χ n N E G), X.p = p → ∀ (H : X.KeyHist) (r : X.AbsRecord),
      X.RecOccurs r → r.1.isRight →
      (∑ θ : Fin (colLen5 (X.p.s n) r.1) → Fin N,
        (∏ h, (X.prior H.1 r.1).w (θ h)) *
          (X.recArrayLaw (X.withCol H r.1 θ)).pr (denominatorFail X (X.withCol H r.1 θ) r)) ≤
        Real.exp (-((p.delta / 4) * X.p.s n)) := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (high_denominator_budget_eventually p)
  refine ⟨n₀, ?_⟩
  intro n hn N E G X hXp H r hr hh
  have hbudget := hn₀ n hn
  rw [← hXp] at hbudget
  simpa only [hXp] using high_denominator_bound_of_budget X H r hr hh
    hbudget.1 hbudget.2.1 hbudget.2.2.1 hbudget.2.2.2

end
end HypercubeRamsey.Lane_sol_s05_1f
