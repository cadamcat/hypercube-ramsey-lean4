import HypercubeRamsey.S09.Map.Device

namespace HypercubeRamsey.Lane_sol_s09_hind

open Real

private theorem power_product (x : ℝ) (hx : 0 < x) (a b e : ℝ) (he : a + b = e) :
    x ^ a * x ^ b = x ^ e := by
  rw [← Real.rpow_add hx, he]

set_option maxHeartbeats 400000 in
/-- Quantitative exponent comparisons for a scale ratio between `x^κ` and `4x^(2κ)`. -/
theorem scale_exponent_comparisons (x R Q W q κ γ d α : ℝ)
    (hx : 1 ≤ x) (hR : 1 ≤ R) (hRx : R ≤ x) (hQ : Q = W * R)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hγ : 0 < γ) (hWlo : x ^ κ ≤ W) (hWhi : W ≤ 4 * x ^ (2 * κ))
    (hqlo : γ / 2 * W ≤ q) (hqhi : q ≤ W)
    (hlog0 : 0 ≤ Real.log x) (hlog : Real.log x ≤ x ^ κ)
    (hdom : 512 * x ^ (3 * κ) ≤ x ^ (7 * κ))
    (hamp : 8 / γ ≤ x ^ (κ * κ))
    (hgap : 4160 * x ^ (12 * κ) ≤ d * x ^ α) :
    64 * q * Q * Real.log x + 2 * (x ^ (8 * κ) * Q ^ (1 - κ)) ≤
        q * x ^ (8 * κ) * R ^ (1 - κ) ∧
      64 * q * Q * Real.log x + 2 * q + 2 * (x ^ (8 * κ) * Q ^ (1 - κ)) ≤
        d * x ^ α * R / q := by
  have hxpos : 0 < x := by linarith
  have hRpos : 0 < R := by linarith
  have hWpos : 0 < W := (Real.rpow_pos_of_pos hxpos κ).trans_le hWlo
  have hqpos : 0 < q := (mul_pos (div_pos hγ (by norm_num)) hWpos).trans_le hqlo
  have hW1 : 1 ≤ W := (Real.one_le_rpow hx hκ.le).trans hWlo
  have hQ1 : 1 ≤ Q := by rw [hQ]; nlinarith only [hW1, hR]
  have hQpos : 0 < Q := by linarith
  have hRκ : R ^ κ ≤ x ^ κ := Real.rpow_le_rpow hRpos.le hRx hκ.le
  have hRθ : 0 ≤ R ^ (1 - κ) := Real.rpow_nonneg hRpos.le _
  have hsplitR : R ^ (1 - κ) * R ^ κ = R := by
    rw [← Real.rpow_add hRpos]
    convert Real.rpow_one R using 1 <;> ring
  have hRlower : R / x ^ κ ≤ R ^ (1 - κ) := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hxpos κ)).mpr
    calc
      R = R ^ (1 - κ) * R ^ κ := hsplitR.symm
      _ ≤ R ^ (1 - κ) * x ^ κ := mul_le_mul_of_nonneg_left hRκ hRθ
  have hClo : q * x ^ (7 * κ) * R ≤ q * x ^ (8 * κ) * R ^ (1 - κ) := by
    calc
      _ = q * x ^ (8 * κ) * (R / x ^ κ) := by
        have hp := power_product x hxpos (7 * κ) κ (8 * κ) (by ring)
        have hxκne : x ^ κ ≠ 0 := (Real.rpow_pos_of_pos hxpos κ).ne'
        rw [← hp]
        field_simp [hxκne]
        <;> ring
      _ ≤ q * x ^ (8 * κ) * R ^ (1 - κ) := by gcongr
  have hQlog : Q * Real.log x ≤ 4 * x ^ (3 * κ) * R := by
    calc
      _ = W * R * Real.log x := by rw [hQ]
      _ ≤ (4 * x ^ (2 * κ)) * R * x ^ κ := by gcongr
      _ = 4 * x ^ (3 * κ) * R := by
        have hp := power_product x hxpos (2 * κ) κ (3 * κ) (by ring)
        rw [← hp]
        ring
  have hAdom : 2 * (64 * q * Q * Real.log x) ≤ q * x ^ (8 * κ) * R ^ (1 - κ) := by
    calc
      _ ≤ 512 * q * x ^ (3 * κ) * R := by nlinarith only [mul_le_mul_of_nonneg_left hQlog hqpos.le]
      _ = q * (512 * x ^ (3 * κ)) * R := by ring
      _ ≤ q * x ^ (7 * κ) * R := by gcongr
      _ ≤ q * x ^ (8 * κ) * R ^ (1 - κ) := hClo
  have hWκ : x ^ (κ * κ) ≤ W ^ κ := by
    calc
      _ = (x ^ κ) ^ κ := Real.rpow_mul hxpos.le κ κ
      _ ≤ W ^ κ := Real.rpow_le_rpow (Real.rpow_nonneg hxpos.le _) hWlo hκ.le
  have hγWκ : 4 ≤ γ / 2 * W ^ κ := by
    have hh : 8 / γ ≤ W ^ κ := hamp.trans hWκ
    have hh' := (div_le_iff₀ hγ).mp hh
    nlinarith only [hh']
  have hqθ : 4 * W ^ (1 - κ) ≤ q := by
    calc
      _ ≤ (γ / 2 * W ^ κ) * W ^ (1 - κ) :=
        mul_le_mul_of_nonneg_right hγWκ (Real.rpow_nonneg hWpos.le _)
      _ = γ / 2 * W := by
        have hp : W ^ κ * W ^ (1 - κ) = W := by
          rw [← Real.rpow_add hWpos]
          convert Real.rpow_one W using 1 <;> ring
        calc
          (γ / 2 * W ^ κ) * W ^ (1 - κ) = γ / 2 * (W ^ κ * W ^ (1 - κ)) := by ring
          _ = γ / 2 * W := by rw [hp]
      _ ≤ q := hqlo
  have hTdom : 4 * (x ^ (8 * κ) * Q ^ (1 - κ)) ≤ q * x ^ (8 * κ) * R ^ (1 - κ) := by
    calc
      _ = (4 * W ^ (1 - κ)) * x ^ (8 * κ) * R ^ (1 - κ) := by
        rw [hQ, Real.mul_rpow hWpos.le hRpos.le]
        ring
      _ ≤ q * x ^ (8 * κ) * R ^ (1 - κ) := by gcongr
  refine ⟨by linarith, ?_⟩
  have hqUpper : q ≤ 4 * x ^ (2 * κ) := hqhi.trans hWhi
  have hAupper : 64 * q * Q * Real.log x ≤ 1024 * x ^ (5 * κ) * R := by
    calc
      _ ≤ 64 * (4 * x ^ (2 * κ)) * (4 * x ^ (3 * κ) * R) := by
        have hh := mul_le_mul hqUpper hQlog (mul_nonneg hQpos.le hlog0)
          (by positivity : 0 ≤ 4 * x ^ (2 * κ))
        nlinarith only [hh]
      _ = 1024 * x ^ (5 * κ) * R := by
        have hp := power_product x hxpos (2 * κ) (3 * κ) (5 * κ) (by ring)
        rw [← hp]
        ring
  have hx5 : x ^ (5 * κ) ≤ x ^ (10 * κ) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hAupper' : 64 * q * Q * Real.log x ≤ 1024 * x ^ (10 * κ) * R :=
    hAupper.trans (by gcongr)
  have hx2 : x ^ (2 * κ) ≤ x ^ (10 * κ) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hBupper : 2 * q ≤ 8 * x ^ (10 * κ) * R := by
    have hh : 2 * q ≤ 8 * x ^ (2 * κ) := by linarith
    calc
      2 * q ≤ 8 * x ^ (2 * κ) := hh
      _ ≤ 8 * x ^ (10 * κ) := mul_le_mul_of_nonneg_left hx2 (by norm_num)
      _ = (8 * x ^ (10 * κ)) * 1 := by ring
      _ ≤ (8 * x ^ (10 * κ)) * R := mul_le_mul_of_nonneg_left hR (by positivity)
  have hQθ : Q ^ (1 - κ) ≤ Q := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : 1 - κ ≤ 1)
  have hTupper : x ^ (8 * κ) * Q ^ (1 - κ) ≤ 4 * x ^ (10 * κ) * R := by
    calc
      _ ≤ x ^ (8 * κ) * Q := by gcongr
      _ = x ^ (8 * κ) * (W * R) := by rw [hQ]
      _ ≤ x ^ (8 * κ) * ((4 * x ^ (2 * κ)) * R) := by gcongr
      _ = 4 * x ^ (10 * κ) * R := by
        have hp := power_product x hxpos (8 * κ) (2 * κ) (10 * κ) (by ring)
        rw [← hp]
        ring
  have hDlower : 1040 * x ^ (10 * κ) * R ≤ d * x ^ α * R / q := by
    apply (le_div_iff₀ hqpos).mpr
    calc
      _ ≤ (1040 * x ^ (10 * κ) * R) * (4 * x ^ (2 * κ)) := by gcongr
      _ = 4160 * x ^ (12 * κ) * R := by
        have hp := power_product x hxpos (10 * κ) (2 * κ) (12 * κ) (by ring)
        rw [← hp]
        ring
      _ ≤ d * x ^ α * R := mul_le_mul_of_nonneg_right hgap hRpos.le
  linarith

end HypercubeRamsey.Lane_sol_s09_hind
