import HypercubeRamsey.S16.Producers_q_s16_prod2
import HypercubeRamsey.S16.Producers_sol_s16_prod1

namespace HypercubeRamsey.S16.Lane_sol_s16_prod2
open Classical
open scoped BigOperators

/-- The calibration room bounds the raw pretrim loss at the chosen rate. -/
theorem pretrim_loss (d h : ℕ) (ε : ℝ) (hd : 2 ≤ d)
    (hε : 0 < ε ∧ ε ≤ 1)
    (hroom : 16 * (d : ℝ) ^ 2 * (h + 1 : ℝ) ^ 2 * Real.rpow ε (1 / 16 : ℝ) ≤
      Real.rpow (d : ℝ) (-20)) :
    (h : ℝ) ^ 2 * Real.sqrt ε ≤ Real.rpow (d : ℝ) (-10) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have he : Real.sqrt ε ≤ Real.rpow ε (1 / 16 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hε.1 hε.2 (by norm_num)
  have hh : (h : ℝ) ^ 2 ≤ (h + 1 : ℝ) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) h]
  have hb := mul_le_mul hh he (Real.sqrt_nonneg ε) (sq_nonneg (h + 1 : ℝ))
  have hz : 0 ≤ (h + 1 : ℝ) ^ 2 * Real.rpow ε (1 / 16 : ℝ) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hε.1.le _)
  have hf : 1 ≤ 16 * (d : ℝ) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hf hz
  have hp : Real.rpow (d : ℝ) (-20) ≤ Real.rpow (d : ℝ) (-10) :=
    Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num)
  nlinarith [hroom.trans hp]

/-- A numerical bound for all stage denominators on an internal star. -/
theorem stage_cost (d n m l : ℕ) (a b c : ℝ)
    (hd : 2 ≤ d) (hn : 2 ≤ n)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hbudget : a * b * c ≤ 1 + Real.rpow (n : ℝ) (-3))
    (hmn : m ≤ n)
    (hmd : (m : ℝ) ≤ Real.rpow (d : ℝ) 0.01)
    (hld : (l : ℝ) ≤ Real.rpow (d : ℝ) 0.01) :
    a * Real.exp (Real.rpow (d : ℝ) (-0.05) * m + Real.rpow (d : ℝ) (-0.01) * l) *
      (1 - Real.rpow (d : ℝ) (-10))⁻¹ ^ m * b ^ m * c ^ m ≤ 1000 := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hdpos : (0 : ℝ) < d := by linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : (0 : ℝ) < n := by linarith
  let δ := Real.rpow (d : ℝ) (-10)
  have hδ0 : 0 ≤ δ := Real.rpow_nonneg hdpos.le _
  have hδhalf : δ ≤ 1 / 2 := by
    calc
      δ ≤ Real.rpow (d : ℝ) (-1) :=
        Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num)
      _ = (d : ℝ)⁻¹ := Real.rpow_neg_one _
      _ ≤ 1 / 2 := by
        have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
        simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hd2
  have hmul (x : ℝ) (hx : x ≤ -0.01) :
      Real.rpow (d : ℝ) x * Real.rpow (d : ℝ) 0.01 ≤ 1 := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hdpos]
    simpa using Real.rpow_le_rpow_of_exponent_le hd1 (by linarith : x + 0.01 ≤ 0)
  have hmδ : δ * m ≤ 1 :=
    (mul_le_mul_of_nonneg_left hmd hδ0).trans (hmul (-10) (by norm_num))
  have he1 : Real.rpow (d : ℝ) (-0.05) * m ≤ 1 :=
    (mul_le_mul_of_nonneg_left hmd (Real.rpow_nonneg hdpos.le _)).trans (hmul (-0.05) (by norm_num))
  have he2 : Real.rpow (d : ℝ) (-0.01) * l ≤ 1 :=
    (mul_le_mul_of_nonneg_left hld (Real.rpow_nonneg hdpos.le _)).trans (hmul (-0.01) (by norm_num))
  have hpreDen : 0 < 1 - δ := by linarith
  have hnsmall0 : 0 ≤ Real.rpow (n : ℝ) (-3) := Real.rpow_nonneg hnpos.le _
  have hpre : (1 - δ)⁻¹ ^ m ≤ Real.exp 2 := by
    calc
      _ ≤ (Real.exp (2 * δ)) ^ m := pow_le_pow_left₀ (inv_nonneg.mpr hpreDen.le)
        (Lane_sol_s16_prod1.reciprocal_exp_bound δ ⟨hδ0, hδhalf⟩) m
      _ = Real.exp ((m : ℝ) * (2 * δ)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp 2 := Real.exp_le_exp.mpr (by nlinarith)
  have hden : a * b ^ m * c ^ m ≤ Real.exp 2 := by
    have ha0 : 0 ≤ a := by linarith
    have hb0 : 0 ≤ b := by linarith
    have hc0 : 0 ≤ c := by linarith
    have habc0 : 0 ≤ a * b * c := by positivity
    have hbc1 : 1 ≤ b * c := by
      simpa using mul_le_mul hb hc (by norm_num : (0 : ℝ) ≤ 1) hb0
    have haabc : a ≤ a * b * c := by
      simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left hbc1 ha0
    have hbcabc : b * c ≤ a * b * c := by
      simpa only [one_mul, mul_assoc] using mul_le_mul_of_nonneg_right ha (mul_nonneg hb0 hc0)
    have hmnR : (m : ℝ) + 1 ≤ 2 * n := by
      have hm : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    have hneg : Real.rpow (n : ℝ) (-3) * (n : ℝ) ≤ 1 := by
      calc
        _ = Real.rpow (n : ℝ) (-2) := by
          simpa only [Real.rpow_eq_pow, Real.rpow_one,
            show (-3 : ℝ) + 1 = -2 by norm_num] using (Real.rpow_add hnpos (-3) 1).symm
        _ ≤ 1 := by simpa using Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (-2 : ℝ) ≤ 0)
    calc
      a * b ^ m * c ^ m = a * (b * c) ^ m := by rw [mul_pow]; ring
      _ ≤ (a * b * c) * (a * b * c) ^ m := mul_le_mul haabc
        (pow_le_pow_left₀ (by positivity) hbcabc m) (by positivity) habc0
      _ = (a * b * c) ^ (m + 1) := by rw [pow_succ]; ring
      _ ≤ (1 + Real.rpow (n : ℝ) (-3)) ^ (m + 1) :=
        pow_le_pow_left₀ habc0 hbudget _
      _ ≤ (Real.exp (Real.rpow (n : ℝ) (-3))) ^ (m + 1) :=
        pow_le_pow_left₀ (by linarith) (by simpa [add_comm] using Real.add_one_le_exp (Real.rpow (n : ℝ) (-3))) _
      _ = Real.exp (((m + 1 : ℕ) : ℝ) * Real.rpow (n : ℝ) (-3)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp 2 := by
        apply Real.exp_le_exp.mpr
        push_cast
        have h := mul_le_mul_of_nonneg_right hmnR (Real.rpow_nonneg hnpos.le (-3))
        nlinarith
  calc
    _ = Real.exp (Real.rpow (d : ℝ) (-0.05) * m + Real.rpow (d : ℝ) (-0.01) * l) *
        (1 - δ)⁻¹ ^ m * (a * b ^ m * c ^ m) := by dsimp [δ]; ring
    _ ≤ Real.exp 2 * Real.exp 2 * Real.exp 2 := by
      apply mul_le_mul
      · exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) hpre (by positivity) (Real.exp_pos _).le
      · exact hden
      · positivity
      · positivity
    _ = Real.exp (6 : ℝ) := by rw [← Real.exp_add, ← Real.exp_add]; norm_num
    _ ≤ 3 ^ (6 : ℕ) := by
      rw [show (6 : ℝ) = (6 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le _
    _ ≤ 1000 := by norm_num

end HypercubeRamsey.S16.Lane_sol_s16_prod2
