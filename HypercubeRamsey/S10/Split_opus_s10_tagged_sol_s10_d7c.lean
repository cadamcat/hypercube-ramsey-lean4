import HypercubeRamsey.Framework.FinProbLemmas

/-!
Finite posterior integration for the even comparison mean in Section 10.
The data mass is allowed to vanish. A subdensity with total mass at most one
then bounds the integrated posterior by its prior, including after a bounded
data-dependent normalization or gate.
-/

namespace HypercubeRamsey.Lane_sol_s10_d7c

open scoped BigOperators

variable {W Y : Type*} [Fintype W]

/-- Cancellation at one data value, including a zero data marginal. -/
theorem posterior_cancel (π : FinProb W) (F : W → Y → ℝ)
    (hF : ∀ w y, 0 ≤ F w y) (w : W) (y : Y) :
    π.expect (fun u => F u y) *
      (π.w w * F w y / π.expect (fun u => F u y)) = π.w w * F w y := by
  classical
  by_cases hm : π.expect (fun u => F u y) = 0
  · have hle : π.w w * F w y ≤ π.expect (fun u => F u y) := by
      exact Finset.single_le_sum
        (fun u _ => mul_nonneg (π.nonneg u) (hF u y)) (Finset.mem_univ w)
    have hz : π.w w * F w y = 0 :=
      le_antisymm (by simpa [hm] using hle) (mul_nonneg (π.nonneg w) (hF w y))
    simp [hm, hz]
  · field_simp [hm]

variable [Fintype Y]

/-- The finite integration identity, with arbitrary data-dependent test values. -/
theorem posterior_integration_identity (π : FinProb W) (F : W → Y → ℝ)
    (hF : ∀ w y, 0 ≤ F w y) (f : W → Y → ℝ) :
    (∑ y, π.expect (fun w => F w y) *
      ∑ w, f w y * (π.w w * F w y / π.expect (fun u => F u y))) =
        ∑ w, ∑ y, π.w w * f w y * F w y := by
  classical
  simp_rw [Finset.mul_sum]
  calc
    (∑ y, ∑ w, π.expect (fun u => F u y) *
      (f w y * (π.w w * F w y / π.expect (fun u => F u y)))) =
        ∑ y, ∑ w, π.w w * f w y * F w y := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro w _
      rw [show π.expect (fun u => F u y) *
        (f w y * (π.w w * F w y / π.expect (fun u => F u y))) =
          f w y * (π.expect (fun u => F u y) *
            (π.w w * F w y / π.expect (fun u => F u y))) by ring,
        posterior_cancel π F hF w y]
      ring
    _ = _ := Finset.sum_comm

/-- A subdensity integrates the posterior of a nonnegative test to at most
its prior expectation. The total subdensity is the candidate's gate probability. -/
theorem posterior_mean_le_prior (π : FinProb W) (F : W → Y → ℝ)
    (hF : ∀ w y, 0 ≤ F w y) (hgate : ∀ w, ∑ y, F w y ≤ 1)
    (f : W → ℝ) (hf : ∀ w, 0 ≤ f w) :
    (∑ y, π.expect (fun w => F w y) *
      ∑ w, f w * (π.w w * F w y / π.expect (fun u => F u y))) ≤
        π.expect f := by
  rw [posterior_integration_identity π F hF (fun w _ => f w)]
  unfold FinProb.expect
  apply Finset.sum_le_sum
  intro w _
  rw [← Finset.mul_sum]
  exact mul_le_of_le_one_right (mul_nonneg (π.nonneg w) (hf w)) (hgate w)

/-- Gating and light-part normalization cost at most their pointwise bound. -/
theorem bounded_posterior_mean_le_prior (π : FinProb W) (F : W → Y → ℝ)
    (hF : ∀ w y, 0 ≤ F w y) (hgate : ∀ w, ∑ y, F w y ≤ 1)
    (f : W → ℝ) (hf : ∀ w, 0 ≤ f w)
    (g : Y → ℝ) (C : ℝ) (hC : 0 ≤ C) (hg : ∀ y, g y ≤ C) :
    (∑ y, π.expect (fun w => F w y) *
      (g y * ∑ w, f w * (π.w w * F w y / π.expect (fun u => F u y)))) ≤
        C * π.expect f := by
  have hm (y : Y) : 0 ≤ π.expect (fun w => F w y) :=
    Finset.sum_nonneg fun w _ => mul_nonneg (π.nonneg w) (hF w y)
  have hp (y : Y) :
      0 ≤ ∑ w, f w * (π.w w * F w y / π.expect (fun u => F u y)) :=
    Finset.sum_nonneg fun w _ => mul_nonneg (hf w)
      (div_nonneg (mul_nonneg (π.nonneg w) (hF w y)) (hm y))
  calc
    _ ≤ ∑ y, π.expect (fun w => F w y) *
        (C * ∑ w, f w * (π.w w * F w y / π.expect (fun u => F u y))) := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hg y) (hp y)) (hm y)
    _ = C * ∑ y, π.expect (fun w => F w y) *
        ∑ w, f w * (π.w w * F w y / π.expect (fun u => F u y)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ ≤ C * π.expect f := mul_le_mul_of_nonneg_left
      (posterior_mean_le_prior π F hF hgate f hf) hC

end HypercubeRamsey.Lane_sol_s10_d7c
