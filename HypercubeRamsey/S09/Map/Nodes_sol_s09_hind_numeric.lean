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

theorem packing_parameters (R Q ℓ : ℕ) (W γ δ ηp η : ℝ)
    (hR : 1 ≤ R) (hQR : (Q : ℝ) = W * (R : ℝ))
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hδ : 0 < δ)
    (hWγ : 2 / γ ≤ W) (hWδ : 8 / δ ≤ W)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (hgap : δ ≤ η - ηp)
    (hγsmall : 2 * (2 * (ℓ : ℝ) + 1) * γ ≤ δ / 4) :
    let q := ⌊γ * W⌋₊
    0 < q ∧ γ / 2 * W ≤ (q : ℝ) ∧ (q : ℝ) ≤ W ∧
      (η + 1) * ((R : ℝ) + ((2 * ℓ * R + 1 : ℕ) : ℝ) * ((q - 1 : ℕ) : ℝ)) <
        (η - ηp) * (Q : ℝ) := by
  let q := ⌊γ * W⌋₊
  have hW : 0 < W := (div_pos (by norm_num) hγ).trans_le hWγ
  have hWγ' : 2 ≤ W * γ := (div_le_iff₀ hγ).mp hWγ
  have hfloor : (q : ℝ) ≤ γ * W := Nat.floor_le (by positivity)
  have hfloor' : γ * W < (q : ℝ) + 1 := Nat.lt_floor_add_one _
  have hqlo : γ / 2 * W ≤ (q : ℝ) := by nlinarith only [hWγ', hfloor']
  have hqR : 0 < (q : ℝ) := (mul_pos (div_pos hγ (by norm_num)) hW).trans_le hqlo
  have hq : 0 < q := by exact_mod_cast hqR
  have hqhi : (q : ℝ) ≤ W := hfloor.trans (by nlinarith only [hγ1, hW])
  refine ⟨hq, hqlo, hqhi, ?_⟩
  have hRreal : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hQpos : 0 < (Q : ℝ) := by rw [hQR]; positivity
  have hRnonneg : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
  have hsub : ((q - 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.sub_le q 1)
  have hfactor : ((2 * ℓ * R + 1 : ℕ) : ℝ) ≤ (2 * (ℓ : ℝ) + 1) * (R : ℝ) := by
    push_cast
    nlinarith only [hRreal]
  have hRq : (R : ℝ) * (q : ℝ) ≤ γ * (Q : ℝ) := by
    calc
      _ ≤ (R : ℝ) * (γ * W) := mul_le_mul_of_nonneg_left hfloor hRnonneg
      _ = γ * (Q : ℝ) := by rw [hQR]; ring
  have hproduct : ((2 * ℓ * R + 1 : ℕ) : ℝ) * ((q - 1 : ℕ) : ℝ) ≤
      (2 * (ℓ : ℝ) + 1) * γ * (Q : ℝ) := by
    calc
      _ ≤ ((2 * (ℓ : ℝ) + 1) * (R : ℝ)) * (q : ℝ) :=
        mul_le_mul hfactor hsub (by positivity) (by positivity)
      _ = (2 * (ℓ : ℝ) + 1) * ((R : ℝ) * (q : ℝ)) := by ring
      _ ≤ (2 * (ℓ : ℝ) + 1) * (γ * (Q : ℝ)) := mul_le_mul_of_nonneg_left hRq (by positivity)
      _ = _ := by ring
  have hWδ' : 8 ≤ W * δ := (div_le_iff₀ hδ).mp hWδ
  have hRsmall : 8 * (R : ℝ) ≤ δ * (Q : ℝ) := by
    calc
      _ ≤ (W * δ) * (R : ℝ) := mul_le_mul_of_nonneg_right hWδ' hRnonneg
      _ = δ * (Q : ℝ) := by rw [hQR]; ring
  have hγQ := mul_le_mul_of_nonneg_right hγsmall hQpos.le
  have hgapQ := mul_le_mul_of_nonneg_right hgap hQpos.le
  have hδQ : 0 < δ * (Q : ℝ) := mul_pos hδ hQpos
  calc
    _ ≤ (η + 1) * ((R : ℝ) + (2 * (ℓ : ℝ) + 1) * γ * (Q : ℝ)) := by gcongr
    _ ≤ 2 * ((R : ℝ) + (2 * (ℓ : ℝ) + 1) * γ * (Q : ℝ)) := by
      apply mul_le_mul_of_nonneg_right (by linarith : η + 1 ≤ 2)
      positivity
    _ ≤ δ * (Q : ℝ) / 2 := by nlinarith only [hRsmall, hγQ]
    _ < δ * (Q : ℝ) := by linarith
    _ ≤ (η - ηp) * (Q : ℝ) := hgapQ

end HypercubeRamsey.Lane_sol_s09_hind
