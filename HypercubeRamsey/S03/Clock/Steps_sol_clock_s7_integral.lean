import HypercubeRamsey.S03.Clock.Steps_sol_clock_s7_analysis
import HypercubeRamsey.Framework.FinProbLemmas

set_option autoImplicit false

namespace HypercubeRamsey.Lane_sol_clock_s7

open scoped BigOperators

/-- Summing all distinguished time tuples factors as a power of the one-target integral. -/
theorem target_tuple_integral {I : Type*} [Fintype I] [DecidableEq I]
    {T : ℕ} (δ : ℝ) (f : Fin T → ℝ) :
    δ ^ Fintype.card I * (∑ times : I → Fin T, ∏ i, f (times i)) =
      (δ * ∑ t, f t) ^ Fintype.card I := by
  classical
  calc
    _ = ∑ times : I → Fin T, ∏ i, δ * f (times i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro times _
      rw [Finset.prod_mul_distrib]
      simp
    _ = ∏ _i : I, ∑ t : Fin T, δ * f t := (Fintype.prod_sum (fun (_i : I) t => δ * f t)).symm
    _ = _ := by simp [← Finset.mul_sum]

/-- The background exception remains relative after integrating all target times. -/
theorem target_integral_with_exception {I Ω : Type*}
    [Fintype I] [DecidableEq I] [Fintype Ω]
    {T : ℕ} (P : FinProb Ω) (Good : Ω → Prop)
    (δ C ε : ℝ) (f : Fin T → ℝ)
    (integrand : (I → Fin T) → Ω → ℝ)
    (hδ : 0 ≤ δ) (hC : 0 ≤ C) (hf : ∀ t, 0 ≤ f t)
    (hgood : ∀ times ω, Good ω → integrand times ω ≤ C * ∏ i, f (times i))
    (hbad : ∀ times ω, integrand times ω ≤ 1)
    (hexception : P.pr (fun ω => ¬ Good ω) ≤ ε)
    (hintegral : δ * ∑ t, f t ≤ 1) :
    δ ^ Fintype.card I * (∑ times : I → Fin T, P.expect (integrand times)) ≤
      C + ε * (δ * (T : ℝ)) ^ Fintype.card I := by
  classical
  have hindicator : P.expect (fun ω => if Good ω then 0 else 1) =
      P.pr (fun ω => ¬ Good ω) := by
    unfold FinProb.expect FinProb.pr
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : Good ω <;> simp [h]
  have htime (times : I → Fin T) :
      P.expect (integrand times) ≤ C * (∏ i, f (times i)) + ε := by
    have hprod : 0 ≤ C * ∏ i, f (times i) :=
      mul_nonneg hC (Finset.prod_nonneg (by intro i _; exact hf (times i)))
    calc
      _ ≤ P.expect (fun ω => C * (∏ i, f (times i)) + if Good ω then 0 else 1) := by
        apply FinProb.expect_mono
        intro ω
        by_cases h : Good ω
        · simpa [h] using hgood times ω h
        · simpa [h] using (hbad times ω).trans (by linarith : (1 : ℝ) ≤ C * (∏ i, f (times i)) + 1)
      _ = C * (∏ i, f (times i)) + P.pr (fun ω => ¬ Good ω) := by
        rw [FinProb.expect_add, FinProb.expect_const, hindicator]
      _ ≤ _ := add_le_add le_rfl hexception
  have hbase : 0 ≤ δ * ∑ t, f t :=
    mul_nonneg hδ (Finset.sum_nonneg (by intro t _; exact hf t))
  have hpow : (δ * ∑ t, f t) ^ Fintype.card I ≤ 1 := pow_le_one₀ hbase hintegral
  calc
    _ ≤ δ ^ Fintype.card I * (∑ times : I → Fin T, (C * (∏ i, f (times i)) + ε)) := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (by intro times _; exact htime times))
        (pow_nonneg hδ _)
    _ = C * (δ ^ Fintype.card I * (∑ times : I → Fin T, ∏ i, f (times i))) +
        ε * (δ * (T : ℝ)) ^ Fintype.card I := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
        Fintype.card_fin, Nat.cast_pow]
      rw [mul_pow]
      ring
    _ ≤ _ := by
      rw [target_tuple_integral]
      have hfirst : C * (δ * ∑ t, f t) ^ Fintype.card I ≤ C := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hC
      exact add_le_add hfirst le_rfl

end HypercubeRamsey.Lane_sol_clock_s7
