import HypercubeRamsey.Framework.FinProb

namespace HypercubeRamsey.FinProb

open scoped BigOperators

/-- A finite union bound for the real-weight finite probability interface. -/
theorem pr_iUnion_le {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (P : FinProb Ω) (A : ι → Ω → Prop) :
    P.pr (fun ω => ∃ i, A i ω) ≤ ∑ i, P.pr (A i) := by
  classical
  letI : DecidablePred (fun ω => ∃ i, A i ω) :=
    fun ω => Classical.propDecidable _
  unfold FinProb.pr
  calc
    (∑ ω, if ∃ i, A i ω then P.w ω else 0) ≤
        ∑ ω, P.w ω * ∑ i, if A i ω then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases he : ∃ i, A i ω
      · rcases he with ⟨i, hi⟩
        have hExists : ∃ j, A j ω := ⟨i, hi⟩
        let f : ι → ℝ := fun j => if A j ω then 1 else 0
        have hf : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ f j := by
          intro j hj
          by_cases hAj : A j ω <;> simp [f, hAj]
        have hcount : 1 ≤ ∑ j, if A j ω then (1 : ℝ) else 0 := by
          calc
            1 = (if A i ω then (1 : ℝ) else 0) := by simp [hi]
            _ ≤ ∑ j, if A j ω then (1 : ℝ) else 0 :=
              Finset.single_le_sum (s := Finset.univ) (f := f) hf
                (Finset.mem_univ i)
        have hweight : P.w ω ≤ P.w ω * ∑ j, if A j ω then (1 : ℝ) else 0 := by
          simpa using mul_le_mul_of_nonneg_left hcount (P.nonneg ω)
        rw [if_pos hExists]
        exact hweight
      · have hcount : 0 ≤ ∑ j, if A j ω then (1 : ℝ) else 0 :=
          Finset.sum_nonneg (fun j hj => by
            by_cases hAj : A j ω <;> simp [hAj])
        rw [if_neg he]
        exact mul_nonneg (P.nonneg ω) hcount
    _ = ∑ ω, ∑ i, P.w ω * (if A i ω then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro ω hω
      rw [Finset.mul_sum]
    _ = ∑ i, ∑ ω, P.w ω * (if A i ω then (1 : ℝ) else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ ω, if A i ω then P.w ω else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases hA : A i ω <;> simp [hA]
    _ = ∑ i, P.pr (A i) := by simp [FinProb.pr]

/-- The probability of an event and its complement sum to one. -/
theorem pr_add_pr_not {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) : P.pr A + P.pr (fun ω => ¬ A ω) = 1 := by
  classical
  unfold FinProb.pr
  rw [← Finset.sum_add_distrib, ← P.sum_eq_one]
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hA : A ω <;> simp [hA]

end HypercubeRamsey.FinProb
