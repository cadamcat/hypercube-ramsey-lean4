import HypercubeRamsey.PartC.Cleaning
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace HypercubeRamsey.S18.Lane_sol_s18_2i

open Classical
open scoped BigOperators

set_option maxHeartbeats 400000

/-- The degree-window proof has a coefficient depending on its drift bound. -/
theorem normalized_single_power_le {q b : ℝ} (hq : 0 ≤ q)
    (hqb : q ≤ 1 / 2 + b) (d : ℕ) :
    ((2 : ℝ) ^ d * q ^ d) ^ 2 ≤ Real.exp (4 * d * b) := by
  have hbase : 2 * q ≤ Real.exp (2 * b) := by
    have he := Real.add_one_le_exp (2 * b)
    linarith
  calc
    ((2 : ℝ) ^ d * q ^ d) ^ 2 = (2 * q) ^ (2 * d) := by
      rw [← mul_pow, ← pow_mul]
      congr 1
      omega
    _ ≤ (Real.exp (2 * b)) ^ (2 * d) :=
      pow_le_pow_left₀ (by positivity) hbase _
    _ = Real.exp (4 * d * b) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

/-- Weighted relaxed row tails already control the correlation part of the
pair moment; this uses no source-discrepancy hypothesis. -/
theorem row_tail_exponential_sum {N : ℕ} {E : Fin N → Fin N → Prop}
    {c : Colour} {π : Fin N → ℝ} {A : Finset (Fin N)} {n ξ : ℝ}
    {x : Fin N} (hn : 0 ≤ n) (hξ : 0 ≤ ξ)
    (hrow : RowTailRelaxed E c π A n ξ x) :
    (∑ z ∈ A, if |corr E c π x z| ≤ ξ then
      Real.exp (2 * n * |corr E c π x z|) else 0) ≤
      (Real.exp (2 * n * Real.rpow n (-1.02)) +
        Real.exp (-Real.rpow n 0.19)) * A.card := by
  let τ := Real.rpow n (-1.02)
  have hpoint (z : Fin N) :
      (if |corr E c π x z| ≤ ξ then Real.exp (2 * n * |corr E c π x z|) else 0) ≤
        Real.exp (2 * n * τ) +
          (if τ < |corr E c π x z| ∧ |corr E c π x z| ≤ 2 * ξ then
            Real.exp (100 * n * |corr E c π x z|) else 0) := by
    by_cases hc : |corr E c π x z| ≤ ξ
    · rw [if_pos hc]
      by_cases ht : τ < |corr E c π x z|
      · rw [if_pos ⟨ht, by linarith⟩]
        have he : Real.exp (2 * n * |corr E c π x z|) ≤
            Real.exp (100 * n * |corr E c π x z|) := by
          apply Real.exp_le_exp.mpr
          nlinarith [abs_nonneg (corr E c π x z)]
        linarith [Real.exp_pos (2 * n * τ)]
      · have he : Real.exp (2 * n * |corr E c π x z|) ≤
            Real.exp (2 * n * τ) := by
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_left (le_of_not_gt ht) (by positivity)
        have hz : 0 ≤ (if τ < |corr E c π x z| ∧ |corr E c π x z| ≤ 2 * ξ then
            Real.exp (100 * n * |corr E c π x z|) else 0) := by
          split_ifs <;> positivity
        linarith
    · rw [if_neg hc]
      split_ifs <;> positivity
  have hsum := Finset.sum_le_sum (s := A) (fun z _ => hpoint z)
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  have htail :
      (∑ z ∈ A, if τ < |corr E c π x z| ∧ |corr E c π x z| ≤ 2 * ξ then
        Real.exp (100 * n * |corr E c π x z|) else 0) ≤
      Real.exp (-Real.rpow n 0.19) * A.card := by
    simpa only [τ, Finset.sum_filter] using hrow.2
  dsimp only [τ] at hsum htail
  nlinarith

/-- A scalar diagnostic for the frozen coefficient, rather than a
counterexample to Stage or LateData. Even the drift g/n (within the direct
degree window) gives a squared normalized moment greater than exp(2g)
when at least three quarters of the coordinates survive. -/
theorem normalized_single_power_gt {n d : ℕ} {g : ℝ}
    (hn : 0 < (n : ℝ)) (hg : 0 < g) (hgn : g ≤ (n : ℝ) / 2)
    (hd : 3 * n ≤ 4 * d) :
    Real.exp (2 * g) <
      ((2 : ℝ) ^ d * (1 / 2 + g / n) ^ d) ^ 2 := by
  have hfrac : 0 < 2 * g / (n : ℝ) := by positivity
  have hl := Real.lt_log_one_add_of_pos hfrac
  have hratio : (4 * g) / (3 * (n : ℝ)) ≤
      2 * (2 * g / (n : ℝ)) / (2 * g / (n : ℝ) + 2) := by
    have hden : 0 < 2 * g / (n : ℝ) + 2 := by positivity
    have hng : 0 < (n : ℝ) + g := by positivity
    have heq : 2 * (2 * g / (n : ℝ)) / (2 * g / (n : ℝ) + 2) =
        2 * g / ((n : ℝ) + g) := by
      field_simp [hn.ne', hden.ne', hng.ne']
      <;> ring
    rw [heq]
    apply (div_le_div_iff₀ (by positivity : 0 < 3 * (n : ℝ)) hng).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hgn) hg.le]
  have hlog : (4 * g) / (3 * (n : ℝ)) < Real.log (1 + 2 * g / (n : ℝ)) :=
    hratio.trans_lt hl
  have hdR : 3 * (n : ℝ) ≤ 4 * (d : ℝ) := by exact_mod_cast hd
  have hdpos : 0 < (d : ℝ) := by nlinarith
  have hlogmul := mul_lt_mul_of_pos_left hlog (by positivity : 0 < 2 * (d : ℝ))
  have hlow : 2 * g ≤ 2 * (d : ℝ) * ((4 * g) / (3 * (n : ℝ))) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : 0 < 3 * (n : ℝ))).mpr
    nlinarith [mul_le_mul_of_nonneg_right hdR hg.le]
  have hexp := Real.exp_lt_exp.mpr (hlow.trans_lt hlogmul)
  have hbase : 0 < 1 + 2 * g / (n : ℝ) := by positivity
  calc
    Real.exp (2 * g) <
        Real.exp ((2 * (d : ℝ)) * Real.log (1 + 2 * g / (n : ℝ))) := hexp
    _ = (1 + 2 * g / (n : ℝ)) ^ (2 * d) := by
      rw [show (2 * (d : ℝ)) = ((2 * d : ℕ) : ℝ) by norm_cast,
        Real.exp_nat_mul, Real.exp_log hbase]
    _ = ((2 : ℝ) ^ d * (1 / 2 + g / n) ^ d) ^ 2 := by
      rw [← mul_pow, ← pow_mul]
      have heq : (1 + 2 * g / (n : ℝ)) = 2 * (1 / 2 + g / n) := by ring
      rw [heq]
      congr 1
      omega

/-- The scalar degree-window hypotheses do not imply the coefficient KB. -/
theorem cutoff_coefficient_obstruction {n d : ℕ} {g K : ℝ}
    (hn : 0 < (n : ℝ)) (hg : 0 < g) (hgn : g ≤ (n : ℝ) / 2)
    (hd : 3 * n ≤ 4 * d) (hcut : K * Real.log (n : ℝ) ≤ 2 * g) :
    Real.exp (K * Real.log (n : ℝ)) <
      ((2 : ℝ) ^ d * (1 / 2 + g / n) ^ d) ^ 2 :=
  (Real.exp_le_exp.mpr hcut).trans_lt (normalized_single_power_gt hn hg hgn hd)

end HypercubeRamsey.S18.Lane_sol_s18_2i
