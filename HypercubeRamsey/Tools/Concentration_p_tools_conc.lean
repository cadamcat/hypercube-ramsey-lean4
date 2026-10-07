import HypercubeRamsey.Framework.FinProb
import Mathlib.Probability.Moments.SubGaussian

/-!
# Helpers for finite concentration proofs

Bridge finite real-weight laws to Mathlib's PMF measure interface.
-/

namespace HypercubeRamsey

open scoped BigOperators
open MeasureTheory

namespace FinProb

variable {Ω : Type*} [Fintype Ω]

/-- The PMF associated to a finite law with real weights. -/
noncomputable def toPMF (P : FinProb Ω) : PMF Ω :=
  PMF.ofFintype (fun ω => ENNReal.ofReal (P.w ω)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (f := P.w)]
    · simp [P.sum_eq_one]
    · intro ω hω
      exact P.nonneg ω)

/-- Integrals under the PMF measure are the finite expectations. -/
theorem integral_toPMF_eq_expect [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (P : FinProb Ω) (f : Ω → ℝ) :
    ∫ ω, f ω ∂(P.toPMF.toMeasure) = P.expect f := by
  classical
  rw [PMF.integral_eq_sum]
  simp [FinProb.expect, FinProb.toPMF, ENNReal.toReal_ofReal, P.nonneg]

/-- Expectations of coordinate products factor under a finite product law. -/
theorem expect_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (f : ∀ i, Ω i → ℝ) :
    (FinProb.pi P).expect (fun ω => ∏ i, f i (ω i)) =
      ∏ i, (P i).expect (f i) := by
  classical
  change (∑ ω : ∀ i, Ω i, (∏ i, (P i).w (ω i)) * ∏ i, f i (ω i)) =
    ∏ i, ∑ x, (P i).w x * f i x
  calc
    _ = ∑ ω : ∀ i, Ω i, ∏ i, (P i).w (ω i) * f i (ω i) := by
      apply Finset.sum_congr rfl
      intro ω hω
      exact (Finset.univ.prod_mul_distrib
        (f := fun i => (P i).w (ω i)) (g := fun i => f i (ω i))).symm
    _ = ∏ i, ∑ x, (P i).w x * f i x :=
      (Fintype.prod_sum (fun i x => (P i).w x * f i x)).symm

/-- The exponential moment of a sum factors under a finite product law. -/
theorem expect_exp_sum_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (X : ∀ i, Ω i → ℝ) (s : ℝ) :
    (FinProb.pi P).expect (fun ω => Real.exp (s * ∑ i, X i (ω i))) =
      ∏ i, (P i).expect (fun x => Real.exp (s * X i x)) := by
  have hexp (ω : ∀ i, Ω i) :
      Real.exp (s * ∑ i, X i (ω i)) = ∏ i, Real.exp (s * X i (ω i)) := by
    rw [Finset.mul_sum, Real.exp_sum]
  calc
    _ = (FinProb.pi P).expect (fun ω => ∏ i, Real.exp (s * X i (ω i))) := by
      change (∑ ω, (FinProb.pi P).w ω * Real.exp (s * ∑ i, X i (ω i))) =
        ∑ ω, (FinProb.pi P).w ω * ∏ i, Real.exp (s * X i (ω i))
      apply Finset.sum_congr rfl
      intro ω hω
      rw [hexp]
    _ = ∏ i, (P i).expect (fun x => Real.exp (s * X i x)) :=
      expect_pi_prod P (fun i x => Real.exp (s * X i x))

/-- A `[0,1]`-valued variable has the usual exponential-moment bound. -/
theorem expect_exp_mul_le_of_mem_Icc (P : FinProb Ω) (X : Ω → ℝ)
    (hX : ∀ ω, 0 ≤ X ω ∧ X ω ≤ 1) (s : ℝ) :
    P.expect (fun ω => Real.exp (s * X ω)) ≤
      Real.exp ((Real.exp s - 1) * P.expect X) := by
  have hsec (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
      Real.exp (s * x) ≤ 1 + x * (Real.exp s - 1) := by
    have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ s)
      (sub_nonneg.mpr hx1) hx (by ring : (1 - x) + x = 1)
    have h' : Real.exp (x * s) ≤ (1 - x) + x * Real.exp s := by
      simpa [smul_eq_mul] using h
    calc
      Real.exp (s * x) = Real.exp (x * s) := by rw [mul_comm]
      _ ≤ (1 - x) + x * Real.exp s := h'
      _ = 1 + x * (Real.exp s - 1) := by ring
  calc
    P.expect (fun ω => Real.exp (s * X ω)) =
        ∑ ω, P.w ω * Real.exp (s * X ω) := rfl
    _ ≤ ∑ ω, P.w ω * (1 + X ω * (Real.exp s - 1)) := by
      apply Finset.sum_le_sum
      intro ω hω
      exact mul_le_mul_of_nonneg_left (hsec (X ω) (hX ω).1 (hX ω).2) (P.nonneg ω)
    _ = 1 + (Real.exp s - 1) * P.expect X := by
      simp only [mul_add]
      rw [Finset.sum_add_distrib]
      simp only [mul_one, P.sum_eq_one]
      have hfactor :
          (∑ ω, P.w ω * (X ω * (Real.exp s - 1))) =
            (Real.exp s - 1) * P.expect X := by
        calc
          _ = (∑ ω, P.w ω * X ω) * (Real.exp s - 1) := by
            calc
              _ = ∑ ω, (P.w ω * X ω) * (Real.exp s - 1) := by
                apply Finset.sum_congr rfl
                intro ω hω
                ring
              _ = (∑ ω, P.w ω * X ω) * (Real.exp s - 1) :=
                (Finset.univ.sum_mul (fun ω => P.w ω * X ω) _).symm
          _ = (Real.exp s - 1) * P.expect X := by
            rw [FinProb.expect]
            ring
      rw [hfactor]
    _ ≤ Real.exp ((Real.exp s - 1) * P.expect X) := by
      simpa [add_comm] using Real.add_one_le_exp ((Real.exp s - 1) * P.expect X)

/-- The `[0,1]` exponential-moment bound tensorizes over a finite product. -/
theorem expect_exp_sum_le_of_mem_Icc {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (X : ∀ i, Ω i → ℝ) (hX : ∀ i ω, 0 ≤ X i ω ∧ X i ω ≤ 1) (s : ℝ) :
    (FinProb.pi P).expect (fun ω => Real.exp (s * ∑ i, X i (ω i))) ≤
      Real.exp ((Real.exp s - 1) * ∑ i, (P i).expect (X i)) := by
  calc
    (FinProb.pi P).expect (fun ω => Real.exp (s * ∑ i, X i (ω i))) =
        ∏ i, (P i).expect (fun x => Real.exp (s * X i x)) :=
      expect_exp_sum_pi P X s
    _ ≤ ∏ i, Real.exp ((Real.exp s - 1) * (P i).expect (X i)) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        unfold FinProb.expect
        apply Finset.sum_nonneg
        intro ω hω
        exact mul_nonneg ((P i).nonneg ω) (Real.exp_nonneg _)
      · intro i hi
        exact expect_exp_mul_le_of_mem_Icc (P i) (X i) (hX i) s
    _ = Real.exp ((Real.exp s - 1) * ∑ i, (P i).expect (X i)) := by
      rw [← Real.exp_sum]
      congr 1
      rw [← Finset.mul_sum]

/-- Finite Markov inequality in exponential form. -/
theorem pr_exp_markov (P : FinProb Ω) (Y : Ω → ℝ) (s ε : ℝ) (hs : 0 ≤ s) :
    P.pr (fun ω => ε ≤ Y ω) ≤
      Real.exp (-s * ε) * P.expect (fun ω => Real.exp (s * Y ω)) := by
  classical
  calc
    P.pr (fun ω => ε ≤ Y ω) =
        ∑ ω, if ε ≤ Y ω then P.w ω else 0 := rfl
    _ ≤ ∑ ω, P.w ω * (Real.exp (-s * ε) * Real.exp (s * Y ω)) := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases h : ε ≤ Y ω
      · have he : 1 ≤ Real.exp (-s * ε) * Real.exp (s * Y ω) := by
          rw [← Real.exp_add]
          apply (Real.one_le_exp_iff).2
          nlinarith [mul_le_mul_of_nonneg_left h hs]
        simpa [h] using mul_le_mul_of_nonneg_left he (P.nonneg ω)
      · simp [h]
        exact mul_nonneg (P.nonneg ω)
          (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = Real.exp (-s * ε) * P.expect (fun ω => Real.exp (s * Y ω)) := by
      simp [FinProb.expect, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- Probability is monotone under event inclusion. -/
theorem pr_mono (P : FinProb Ω) (A B : Ω → Prop)
    (hAB : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω
  · have hB := hAB ω hA
    simp [hA, hB]
  · by_cases hB : B ω <;> simp [hA, hB, P.nonneg ω]

/-- The probability of a union is at most the sum of its probabilities. -/
theorem pr_union_le (P : FinProb Ω) (A B : Ω → Prop) :
    P.pr (fun ω => A ω ∨ B ω) ≤ P.pr A + P.pr B := by
  classical
  unfold FinProb.pr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω
  · by_cases hB : B ω
    · simp [hA, hB]
      exact P.nonneg ω
    · simp [hA, hB]
  · by_cases hB : B ω <;> simp [hA, hB]

end FinProb

end HypercubeRamsey
