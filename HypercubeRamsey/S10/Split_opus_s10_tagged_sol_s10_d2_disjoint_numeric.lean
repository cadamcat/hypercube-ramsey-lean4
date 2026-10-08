import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d2_candidates

namespace HypercubeRamsey.Lane_sol_s10_d2

open Classical OAI.HypercubeRamsey HypercubeRamsey.S10 Filter
open scoped BigOperators

/-- List enumeration is absorbed by half the fixed-list exponent. -/
theorem disjoint_error_small (δ c ε : ℝ) (hδ : 0 < δ) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ^ n *
        ((((36 * n ^ 16 + 1) ^ p10_1kFixedListBlockCount n δ : ℕ) : ℝ) ^ n *
          (Real.exp (-c * ((n : ℝ) ^ (-δ)) ^ 2 * p10_1kTupleListLength n δ)) ^ n) ≤ ε := by
  have hgap := power_gap (a := 201 * δ) (b := 298 * δ) (c := 768 / (c * δ))
    (by nlinarith) (by positivity)
  have hsmall := cube_exp_error_small (1 + 298 * δ) 0 (c / 2) 1 ε
    (by nlinarith) (by positivity) (by norm_num) hε
  filter_upwards [hgap, hsmall, Filter.eventually_atTop.mpr ⟨2, fun _ hn => hn⟩]
    with n hgap hsmall hn
  let x : ℝ := n
  let R := p10_1kFixedListBlockCount n δ
  let k := p10_1kTupleListLength n δ
  let B : ℝ := 36 * x ^ 16 + 1
  have hx : 0 < x := by dsimp [x]; exact_mod_cast (by omega : 0 < n)
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (by omega : 1 ≤ n)
  have hB : 0 < B := by dsimp [B]; positivity
  have hlog : Real.log B ≤ 128 * Real.log x := by
    have hb : ((36 * n ^ 16 : ℕ) : ℝ) ≤ 36 * (n : ℝ) ^ 16 := by norm_cast
    simpa [B, x] using candidate_log_bound n (36 * n ^ 16) hn hb
  have hround := p10_1kFixedListScale_rounding_bounds n δ hn hδ
  have hR : (R : ℝ) ≤ 3 * x ^ (200 * δ) := hround.2.2
  have hk : x ^ (300 * δ) ≤ (k : ℝ) := Nat.le_ceil _
  have hL : (x ^ (-δ)) ^ 2 * (k : ℝ) ≥ x ^ (298 * δ) := by
    have he : (x ^ (-δ)) ^ 2 * x ^ (300 * δ) = x ^ (298 * δ) := by
      rw [pow_two, ← Real.rpow_add hx, ← Real.rpow_add hx]
      congr 1
      ring
    rw [← he]
    exact mul_le_mul_of_nonneg_left hk (sq_nonneg _)
  have hcost : (R : ℝ) * Real.log B ≤ c / 2 * x ^ (298 * δ) := by
    have hlogX : Real.log x ≤ x ^ δ / δ := Real.log_natCast_le_rpow_div n hδ
    have hlogX0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hcost0 : (R : ℝ) * Real.log B ≤ (384 / δ) * x ^ (201 * δ) := by
      calc
        (R : ℝ) * Real.log B ≤ (R : ℝ) * (128 * Real.log x) :=
          mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
        _ ≤ (3 * x ^ (200 * δ)) * (128 * (x ^ δ / δ)) := by gcongr
        _ = (384 / δ) * x ^ (201 * δ) := by
          rw [show 201 * δ = 200 * δ + δ by ring, Real.rpow_add hx]
          ring
    have hg := mul_lt_mul_of_pos_left hgap (by positivity : 0 < c / 2)
    have he : (c / 2) * (768 / (c * δ) * x ^ (201 * δ)) = (384 / δ) * x ^ (201 * δ) := by
      field_simp [hc.ne', hδ.ne'] <;> norm_num
    have hg' : (384 / δ) * x ^ (201 * δ) < c / 2 * x ^ (298 * δ) := by
      simpa only [he, x] using hg
    exact hcost0.trans hg'.le
  have hBexp : B ^ R = Real.exp ((R : ℝ) * Real.log B) := by
    rw [Real.exp_nat_mul, Real.exp_log hB]
  have hcast : (((36 * n ^ 16 + 1) ^ R : ℕ) : ℝ) = B ^ R := by dsimp [B, x]; norm_cast
  have hper : (((36 * n ^ 16 + 1) ^ R : ℕ) : ℝ) ^ n *
      (Real.exp (-c * (x ^ (-δ)) ^ 2 * k)) ^ n ≤
        Real.exp (-(c / 2) * x ^ (1 + 298 * δ)) := by
    rw [hcast, hBexp, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he : (n : ℝ) * x ^ (298 * δ) = x ^ (1 + 298 * δ) := by
      rw [Real.rpow_add hx, Real.rpow_one]
    have hh : (R : ℝ) * Real.log B - c * (x ^ (-δ)) ^ 2 * k ≤ -c / 2 * x ^ (298 * δ) := by
      nlinarith [hcost, hL]
    have hh' := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg n)
    rw [mul_sub] at hh'
    nlinarith [he, hh']
  apply le_trans (mul_le_mul_of_nonneg_left hper (by positivity))
  simpa [x] using hsmall

end HypercubeRamsey.Lane_sol_s10_d2
