import HypercubeRamsey.S03.Clock.Model
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

namespace HypercubeRamsey.Lane_sol_clock_s7

open Filter

theorem exp_small_error {E : ℝ} (hE0 : 0 ≤ E) (hE1 : E ≤ 1 / 2) :
    Real.exp E ≤ 1 + 2 * E := by
  have hb : 0 < 1 - E := by linarith
  have hmul := mul_le_mul_of_nonneg_left (Real.one_sub_le_exp_neg E) (Real.exp_nonneg E)
  have hprod : Real.exp E * (1 - E) ≤ 1 := by
    simpa [← Real.exp_add] using hmul
  calc
    _ ≤ 1 / (1 - E) := (le_div_iff₀ hb).mpr hprod
    _ ≤ _ := by
      apply (div_le_iff₀ hb).mpr
      nlinarith [mul_nonneg hE0 (show 0 ≤ 1 - 2 * E by linarith)]

theorem target_error_absorption {N E H a : ℝ} (k : ℕ)
    (hN : 2 ≤ N) (hE0 : 0 ≤ E) (hE : E ≤ 1 / (4 * N)) (hH : 0 ≤ H)
    (hHK : H * (k : ℝ) ≤ N ^ a / 2) (hgrowth : 4 * N ≤ N ^ a) :
    Real.exp E + H ^ k * Real.exp (-(N ^ a)) ≤ 1 + N⁻¹ := by
  have hN0 : 0 < N := by linarith
  have hEhalf : E ≤ 1 / 2 := by
    apply hE.trans
    apply (div_le_iff₀ (by positivity : 0 < 4 * N)).mpr
    nlinarith
  have hExp : Real.exp E ≤ 1 + 1 / (2 * N) := by
    calc
      _ ≤ 1 + 2 * E := exp_small_error hE0 hEhalf
      _ ≤ 1 + 2 * (1 / (4 * N)) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hE (by norm_num))
      _ = _ := by field_simp; ring
  have hpowEq : (Real.exp H) ^ k = Real.exp (H * (k : ℝ)) := by
    clear hHK
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, ← Real.exp_add, Nat.cast_succ]
      congr 1
      ring
  have hpow : H ^ k ≤ Real.exp (H * (k : ℝ)) := by
    rw [← hpowEq]
    apply pow_le_pow_left₀ hH
    linarith [Real.add_one_le_exp H]
  have htail : H ^ k * Real.exp (-(N ^ a)) ≤ 1 / (2 * N) := by
    calc
      _ ≤ Real.exp (H * (k : ℝ)) * Real.exp (-(N ^ a)) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
      _ = Real.exp (H * (k : ℝ) - N ^ a) := by rw [← Real.exp_add, sub_eq_add_neg]
      _ ≤ Real.exp (-(N ^ a) / 2) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ Real.exp (-(2 * N)) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := by
        rw [Real.exp_neg, inv_eq_one_div]
        apply one_div_le_one_div_of_le (by positivity : 0 < 2 * N)
        linarith [Real.add_one_le_exp (2 * N)]
  calc
    _ ≤ (1 + 1 / (2 * N)) + 1 / (2 * N) := add_le_add hExp htail
    _ = _ := by rw [inv_eq_one_div]; field_simp; ring

theorem scaled_clock_error_bound (N B A cH cJ δ H J : ℝ) (k : ℕ)
    (hN : 0 < N) (hcH : 0 ≤ cH) (hcJ : 0 ≤ cJ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ N ^ (-A)) (hH0 : 0 ≤ H) (hH : H ≤ cH * N ^ (1 / 2 : ℝ))
    (hJ0 : 0 ≤ J) (hJ : J ≤ cJ * N ^ (1 / 2 : ℝ)) (hk : (k : ℝ) ≤ N ^ B) :
    N * ((k : ℝ) * H * (2 * N ^ (-3 * B) + 2 * J * N ^ (-A) + 6 * δ)) ≤
      2 * cH * N ^ (3 / 2 - 2 * B) +
        2 * cH * cJ * N ^ (B + 2 - A) + 6 * cH * N ^ (B + 3 / 2 - A) := by
  have hp (b : ℝ) : 0 ≤ N ^ b := Real.rpow_nonneg hN.le b
  have hKH : (k : ℝ) * H ≤ cH * N ^ (B + 1 / 2) := by
    calc
      _ ≤ N ^ B * (cH * N ^ (1 / 2 : ℝ)) := mul_le_mul hk hH hH0 (hp B)
      _ = _ := by rw [Real.rpow_add hN]; ring
  have hF : 2 * N ^ (-3 * B) + 2 * J * N ^ (-A) + 6 * δ ≤
      2 * N ^ (-3 * B) + 2 * cJ * N ^ (1 / 2 : ℝ) * N ^ (-A) + 6 * N ^ (-A) := by
    have hj := mul_le_mul_of_nonneg_right hJ (hp (-A))
    nlinarith
  have hF0 : 0 ≤ 2 * N ^ (-3 * B) + 2 * J * N ^ (-A) + 6 * δ := by positivity
  have hNm (b : ℝ) : N * N ^ b = N ^ (1 + b) := by
    simpa using (Real.rpow_add hN 1 b).symm
  have h1 : N * N ^ (B + 1 / 2) * N ^ (-3 * B) = N ^ (3 / 2 - 2 * B) := by
    rw [hNm, ← Real.rpow_add hN]
    congr 1
    ring
  have h2 : N * N ^ (B + 1 / 2) * N ^ (1 / 2 : ℝ) * N ^ (-A) = N ^ (B + 2 - A) := by
    rw [hNm, ← Real.rpow_add hN, ← Real.rpow_add hN]
    congr 1
    ring
  have h3 : N * N ^ (B + 1 / 2) * N ^ (-A) = N ^ (B + 3 / 2 - A) := by
    rw [hNm, ← Real.rpow_add hN]
    congr 1
    ring
  calc
    _ ≤ N * ((cH * N ^ (B + 1 / 2)) *
        (2 * N ^ (-3 * B) + 2 * cJ * N ^ (1 / 2 : ℝ) * N ^ (-A) + 6 * N ^ (-A))) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul hKH hF hF0 (mul_nonneg hcH (hp _))) hN.le
    _ = _ := by
      calc
        _ = 2 * cH * (N * N ^ (B + 1 / 2) * N ^ (-3 * B)) +
            2 * cH * cJ * (N * N ^ (B + 1 / 2) * N ^ (1 / 2 : ℝ) * N ^ (-A)) +
            6 * cH * (N * N ^ (B + 1 / 2) * N ^ (-A)) := by ring
        _ = _ := by rw [h1, h2, h3]

theorem eventual_target_error_caps (B A cH cJ : ℝ) (hB : 1 ≤ B) (hA : 10 * B < A) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      2 * cH * (n : ℝ) ^ (3 / 2 - 2 * B) +
        2 * cH * cJ * (n : ℝ) ^ (B + 2 - A) + 6 * cH * (n : ℝ) ^ (B + 3 / 2 - A) ≤ 1 / 4 ∧
      cH * (n : ℝ) ^ (B + 1 / 2 - A / 3) ≤ 1 / 2 ∧
      4 ≤ (n : ℝ) ^ (A / 3 - 1) := by
  have hpow (b : ℝ) (hb : b < 0) : Tendsto (fun n : ℕ => (n : ℝ) ^ b) atTop (nhds 0) := by
    simpa only [Function.comp_def, neg_neg] using
      (tendsto_rpow_neg_atTop (by linarith : 0 < -b)).comp tendsto_natCast_atTop_atTop
  have hlim := ((hpow (3 / 2 - 2 * B) (by linarith)).const_mul (2 * cH)).add
    ((hpow (B + 2 - A) (by linarith)).const_mul (2 * cH * cJ)) |>.add
      ((hpow (B + 3 / 2 - A) (by linarith)).const_mul (6 * cH))
  have hlim' : Tendsto (fun n : ℕ =>
      2 * cH * (n : ℝ) ^ (3 / 2 - 2 * B) +
        2 * cH * cJ * (n : ℝ) ^ (B + 2 - A) + 6 * cH * (n : ℝ) ^ (B + 3 / 2 - A)) atTop (nhds 0) := by
    simpa using hlim
  obtain ⟨nE, hnE⟩ := Filter.eventually_atTop.1 (hlim'.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)))
  have htail : Tendsto (fun n : ℕ => cH * (n : ℝ) ^ (B + 1 / 2 - A / 3)) atTop (nhds 0) := by
    simpa using (hpow (B + 1 / 2 - A / 3) (by linarith)).const_mul cH
  obtain ⟨nT, hnT⟩ := Filter.eventually_atTop.1 (htail.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  have hgrowth : Tendsto (fun n : ℕ => (n : ℝ) ^ (A / 3 - 1)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < A / 3 - 1)).comp tendsto_natCast_atTop_atTop
  obtain ⟨nG, hnG⟩ := Filter.eventually_atTop.1 (Filter.tendsto_atTop.1 hgrowth 4)
  refine ⟨max nE (max nT nG), ?_⟩
  intro n hn
  refine ⟨(hnE n (le_trans (le_max_left _ _) hn)).le, ?_, ?_⟩
  · exact (hnT n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn)).le
  · exact hnG n (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn)

end HypercubeRamsey.Lane_sol_clock_s7
