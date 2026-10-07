import HypercubeRamsey.S05.History_sol_s05_hist1e_group
import HypercubeRamsey.S05.History_sol_s05_h5l_bounds

namespace HypercubeRamsey.Lane_sol_s05_hist1b

open Classical Filter OAI.HypercubeRamsey
open Lane_sol_s05_h5l
open scoped Topology
noncomputable section
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 1024

variable {γ K' χ : ℝ}

private theorem real_nat_power_exp (M : ℝ) (hM : 0 < M) (k : ℕ) :
    M ^ k = Real.exp ((k : ℝ) * Real.log M) := by
  calc
    _ = (Real.exp (Real.log M)) ^ k := by rw [Real.exp_log hM]
    _ = _ := by rw [← Real.exp_nat_mul]

theorem tendsto_T (p : Params5 γ K' χ) : Tendsto (fun n => (p.T n : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono _ ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 1000)).comp
    (Lane_sol_s05_h1.tendsto_m p))
  intro n
  exact Nat.le_ceil _

theorem T_le_m_eventually (p : Params5 γ K' χ) : ∀ᶠ n : ℕ in atTop, p.T n ≤ p.m n := by
  filter_upwards [(Lane_sol_s05_h1.tendsto_m p).eventually_ge_atTop 1,
    fixed_power_margin p 2 (1 / 1000) 1 (by norm_num)] with n hm hpow
  have hh := (T_upper p n hm).trans hpow
  rw [Real.rpow_one] at hh
  exact_mod_cast hh

/-- The log of the whole pool's mask universe costs at most `T k_*` eventually.
The growing `T` absorbs every fixed `Kh`, `eta`, and segment-rounding constant. -/
theorem pool_log_budget_eventually (p : Params5 γ K' χ) :
    ∀ᶠ n : ℕ in atTop,
      Real.log ((p.poolBlocks n : ℝ) + 1) ≤ (p.T n : ℝ) * ((p.q0 : ℝ) * p.uStarSeg n) := by
  let A : ℝ := p.Kh + (Real.log 4 + 1 / 200) / p.eta
  filter_upwards [(Real.tendsto_log_atTop.comp (Lane_sol_s05_h1.tendsto_m p)).eventually_ge_atTop 1,
    (Lane_sol_s05_h1.tendsto_m p).eventually_ge_atTop 2,
    (tendsto_T p).eventually_ge_atTop A] with n hlog hm hT
  let M : ℝ := p.m n
  let U : ℝ := (p.q0 : ℝ) * p.uStarSeg n
  let B : ℝ := p.usedBlocks n
  have hq : (0 : ℝ) < p.q0 := by exact_mod_cast p.hq0.1
  have hmnat : 1 < p.m n := by exact_mod_cast hm
  have huNat : 0 < p.uStarSeg n := uStarSeg_positive p n hmnat
  have hU1 : 1 ≤ U := by
    have hh : 1 ≤ p.q0 * p.uStarSeg n := by have := Nat.mul_pos p.hq0.1 huNat; omega
    dsimp only [U]
    exact_mod_cast hh
  have hU0 : 0 < U := lt_of_lt_of_le (by norm_num) hU1
  have hU : p.eta * Real.log M ≤ U := by
    have hh : p.eta * Real.log M / p.q0 ≤ (p.uStarSeg n : ℝ) := Nat.le_ceil _
    simpa only [mul_comm] using (div_le_iff₀ hq).1 hh
  have hM0 : 0 < M := by dsimp [M]; linarith
  have hMr : 1 ≤ M ^ (1 / 200 : ℝ) := Real.one_le_rpow (by dsimp [M]; linarith) (by norm_num)
  have hB : B ≤ M ^ (1 / 200 : ℝ) + 1 := by
    have hh := Nat.ceil_lt_add_one (div_nonneg (Real.rpow_nonneg hM0.le (1 / 200 : ℝ)) hU0.le)
    change B < M ^ (1 / 200 : ℝ) / U + 1 at hh
    have hd : M ^ (1 / 200 : ℝ) / U ≤ M ^ (1 / 200 : ℝ) :=
      (div_le_iff₀ hU0).2 (by nlinarith)
    linarith
  have he : 1 ≤ Real.exp (p.Kh * U) := Real.one_le_exp_iff.mpr (mul_nonneg p.hKh.le hU0.le)
  have hpool : (p.poolBlocks n : ℝ) + 1 ≤ Real.exp (p.Kh * U) * (4 * M ^ (1 / 200 : ℝ)) := by
    have hh := Nat.ceil_lt_add_one (mul_nonneg (Real.exp_pos (p.Kh * U)).le (Nat.cast_nonneg (p.usedBlocks n)))
    change (p.poolBlocks n : ℝ) < Real.exp (p.Kh * U) * B + 1 at hh
    have hBp : B + 2 ≤ 4 * M ^ (1 / 200 : ℝ) := by linarith
    have hplus : Real.exp (p.Kh * U) * B + 2 ≤ Real.exp (p.Kh * U) * (B + 2) := by nlinarith
    exact (by linarith : (p.poolBlocks n : ℝ) + 1 ≤ Real.exp (p.Kh * U) * (B + 2)).trans
      (mul_le_mul_of_nonneg_left hBp (Real.exp_pos _).le)
  have hbound : Real.log ((p.poolBlocks n : ℝ) + 1) ≤
      p.Kh * U + Real.log 4 + (1 / 200 : ℝ) * Real.log M := by
    apply (Real.log_le_log (by positivity) hpool).trans
    rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (by positivity), Real.log_exp,
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt (Real.rpow_pos_of_pos hM0 _)),
      Real.log_rpow hM0]
    linarith
  have hcoef : 0 ≤ (Real.log 4 + 1 / 200) / p.eta := by
    exact div_nonneg (by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith) p.heta.1.le
  have hc := mul_le_mul_of_nonneg_left hU hcoef
  have heq : ((Real.log 4 + 1 / 200) / p.eta) * (p.eta * Real.log M) =
      (Real.log 4 + 1 / 200) * Real.log M := by field_simp [ne_of_gt p.heta.1] <;> ring
  rw [heq] at hc
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlogM : 1 ≤ Real.log M := hlog
  have hconst := mul_le_mul_of_nonneg_left hlogM hl4
  have hAU : p.Kh * U + Real.log 4 + (1 / 200 : ℝ) * Real.log M ≤ A * U := by
    dsimp only [A]
    nlinarith
  exact (hbound.trans hAU).trans (mul_le_mul_of_nonneg_right hT hU0.le)

variable {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G)

theorem poolIdx_card_le : X.poolIdx.card ≤ X.p.poolBlocks n := by
  have hs : X.poolIdx.image Fin.val ⊆ Finset.range (X.p.poolBlocks n) := by
    intro i hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (Finset.mem_filter.mp ha).2
  have hh := Finset.card_le_card hs
  rw [Finset.card_image_of_injective X.poolIdx Fin.val_injective, Finset.card_range] at hh
  exact hh

theorem mask_power_exp_bound
    (hbudget : Real.log ((X.p.poolBlocks n : ℝ) + 1) ≤
      (X.p.T n : ℝ) * ((X.p.q0 : ℝ) * X.p.uStarSeg n)) :
    ((X.poolIdx.card + 1 : ℕ) : ℝ) ^ X.p.usedBlocks n ≤
      Real.exp ((X.p.T n : ℝ) * (X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ)) := by
  have hlog : Real.log ((X.poolIdx.card : ℝ) + 1) ≤
      Real.log ((X.p.poolBlocks n : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right (poolIdx_card_le X) 1)
  push_cast
  rw [real_nat_power_exp _ (by positivity)]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (hlog.trans hbudget) (Nat.cast_nonneg (X.p.usedBlocks n))
  nlinarith

def recordCountConstant : ℝ := (signatureConstant : ℝ) + 101

theorem recordCountConstant_pos : 0 < recordCountConstant := by
  unfold recordCountConstant
  positivity

theorem record_group_exp_bound (hm : 2 ≤ X.p.m n) (hD : signatureConstant ≤ X.p.m n)
    (hTlo : 2 ≤ X.p.T n) (hT : X.p.T n ≤ X.p.m n)
    (hpool : Real.log ((X.p.poolBlocks n : ℝ) + 1) ≤
      (X.p.T n : ℝ) * ((X.p.q0 : ℝ) * X.p.uStarSeg n))
    (ℓ : X.Key) (t : CubeVertex (X.p.m n)) (j : ℕ) :
    ((Finset.univ.filter fun r : X.AbsRecord => X.RecOccursAt r t j ∧ r.1 = ℓ).card : ℝ) ≤
      Real.exp (recordCountConstant * ((X.p.T n : ℝ) * Real.log (X.p.T n) +
        ((ℓ.level : ℝ) + 1) * Real.log (X.p.m n) +
          (if ℓ.isLeft ∧ ℓ.level = X.p.J n then
            (X.p.T n : ℝ) * (X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) else 0))) := by
  have hcnt := record_card_polynomial X ℓ t j hm hD hT
  have hr : ((Finset.univ.filter fun r : X.AbsRecord => X.RecOccursAt r t j ∧ r.1 = ℓ).card : ℝ) ≤
      (2 : ℝ) ^ (X.p.T n * signatureConstant) * ((X.p.m n : ℝ) + 1) ^ (50 * (ℓ.level + 1)) *
        (if ℓ.isLeft ∧ ℓ.level = X.p.J n then
          ((X.poolIdx.card + 1 : ℕ) : ℝ) ^ X.p.usedBlocks n else 1) := by
    exact_mod_cast hcnt
  have hM : (2 : ℝ) ≤ X.p.m n := by exact_mod_cast hm
  have hT' : (2 : ℝ) ≤ X.p.T n := by exact_mod_cast hTlo
  have hM0 : (0 : ℝ) < X.p.m n := by linarith
  have hT0 : (0 : ℝ) < X.p.T n := by linarith
  have hlogT : Real.log 2 ≤ Real.log (X.p.T n) := Real.log_le_log (by norm_num) hT'
  have hlogM : 0 ≤ Real.log (X.p.m n) := Real.log_nonneg (by linarith)
  have hlogT0 : 0 ≤ Real.log (X.p.T n) := Real.log_nonneg (by linarith)
  have hlogMp : Real.log ((X.p.m n : ℝ) + 1) ≤ 2 * Real.log (X.p.m n) := by
    apply (Real.log_le_log (by positivity) (show (X.p.m n : ℝ) + 1 ≤ (X.p.m n : ℝ) ^ 2 by nlinarith)).trans
    rw [Real.log_pow]
    norm_num
  let W : ℝ := if ℓ.isLeft ∧ ℓ.level = X.p.J n then
    (X.p.T n : ℝ) * ((X.p.q0 : ℝ) * (X.p.uStarSeg n : ℝ) * (X.p.usedBlocks n : ℝ)) else 0
  have hW : 0 ≤ W := by
    dsimp only [W]
    split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    · exact le_rfl
  have hmask : (if ℓ.isLeft ∧ ℓ.level = X.p.J n then
      ((X.poolIdx.card + 1 : ℕ) : ℝ) ^ X.p.usedBlocks n else 1) ≤ Real.exp W := by
    dsimp only [W]
    split_ifs
    · simpa only [Nat.cast_mul] using mask_power_exp_bound X hpool
    · simp
  have hraw := mul_le_mul_of_nonneg_left hmask
    (show 0 ≤ (2 : ℝ) ^ (X.p.T n * signatureConstant) *
      ((X.p.m n : ℝ) + 1) ^ (50 * (ℓ.level + 1)) from
        mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by positivity) _))
  apply (hr.trans hraw).trans
  rw [real_nat_power_exp 2 (by norm_num), real_nat_power_exp _ (by positivity), ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  push_cast
  have hL : (0 : ℝ) ≤ (ℓ.level : ℝ) + 1 := by positivity
  have hD0 : (0 : ℝ) ≤ signatureConstant := Nat.cast_nonneg _
  have hgen := mul_le_mul_of_nonneg_left hlogT (mul_nonneg (Nat.cast_nonneg (X.p.T n)) hD0)
  have hpol := mul_le_mul_of_nonneg_left hlogMp (mul_nonneg (by norm_num : (0 : ℝ) ≤ 50) hL)
  have hbase : 0 ≤ (X.p.T n : ℝ) * Real.log (X.p.T n) := mul_nonneg hT0.le hlogT0
  have hlev : 0 ≤ ((ℓ.level : ℝ) + 1) * Real.log (X.p.m n) := mul_nonneg hL hlogM
  have hDL := mul_nonneg hD0 hlev
  have hDW := mul_nonneg hD0 hW
  change (X.p.T n : ℝ) * signatureConstant * Real.log 2 +
    50 * ((ℓ.level : ℝ) + 1) * Real.log ((X.p.m n : ℝ) + 1) + W ≤
      recordCountConstant * ((X.p.T n : ℝ) * Real.log (X.p.T n) +
        ((ℓ.level : ℝ) + 1) * Real.log (X.p.m n) + W)
  unfold recordCountConstant
  nlinarith

theorem record_count_budgets_eventually (p : Params5 γ K' χ) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ p.m n ∧ signatureConstant ≤ p.m n ∧
      2 ≤ p.T n ∧ p.T n ≤ p.m n ∧
        Real.log ((p.poolBlocks n : ℝ) + 1) ≤ (p.T n : ℝ) * ((p.q0 : ℝ) * p.uStarSeg n) := by
  filter_upwards [(Lane_sol_s05_h1.tendsto_m p).eventually_ge_atTop 2,
    (Lane_sol_s05_h1.tendsto_m p).eventually_ge_atTop (signatureConstant : ℝ),
    (tendsto_T p).eventually_ge_atTop 2, T_le_m_eventually p, pool_log_budget_eventually p]
    with n hm hD hT hTm hpool
  exact ⟨by exact_mod_cast hm, by exact_mod_cast hD, by exact_mod_cast hT, hTm, hpool⟩

end
end HypercubeRamsey.Lane_sol_s05_hist1b
