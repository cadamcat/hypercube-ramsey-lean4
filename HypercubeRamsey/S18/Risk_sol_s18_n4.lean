import HypercubeRamsey.S18.Defs

namespace HypercubeRamsey.Lane_sol_s18_n4
open Classical
open scoped BigOperators

/-- Restore the closure exception before charging the truncated replay integral. -/
theorem truncatedMarkov {Ω : Type*} [Fintype Ω]
    (P : FinLaw Ω) (gate closure : Ω → Prop) (f : Ω → ℝ)
    (η : ℝ) (hη : 0 < η) (hf : ∀ x, 0 ≤ f x) :
    P.pr (fun x => gate x ∧ η < f x) ≤ P.pr (fun x => gate x ∧ closure x) +
      η⁻¹ * P.E (fun x => if gate x ∧ ¬ closure x then f x else 0) := by
  have hpoint : ∀ x, (if gate x ∧ η < f x then (1 : ℝ) else 0) ≤
      (if gate x ∧ closure x then 1 else 0) +
        η⁻¹ * (if gate x ∧ ¬ closure x then f x else 0) := by
    intro x
    by_cases hg : gate x
    · by_cases hc : closure x
      · simp only [hg, hc, and_self, not_true_eq_false, and_false, ite_true, ite_false, mul_zero, add_zero]
        split_ifs <;> norm_num
      · simp only [hg, hc, true_and, ite_false, not_false_eq_true, and_self, ite_true, zero_add]
        by_cases hfx : η < f x
        · simp only [hfx, ite_true]
          calc
            (1 : ℝ) ≤ f x / η := (le_div_iff₀ hη).2 (by simpa using hfx.le)
            _ = η⁻¹ * f x := by ring
        · simp only [hfx, ite_false]
          exact mul_nonneg (inv_nonneg.mpr hη.le) (hf x)
    · simp [hg]
  unfold FinLaw.pr FinLaw.E
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hx
  have h := mul_le_mul_of_nonneg_left (hpoint x) (P.nonneg x)
  by_cases hg : gate x <;> by_cases hc : closure x <;> by_cases hfx : η < f x <;>
    simpa [hg, hc, hfx, mul_add, mul_assoc, mul_left_comm] using h

/-- A cover by bounded replay patterns controls the whole truncated integral. -/
theorem patternCoverExpectation {Ω I : Type*} [Fintype Ω] [Fintype I]
    (P : FinLaw Ω) (patterns : Finset I) (truncated : Ω → Prop)
    (consistent : I → Ω → Prop) (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hcover : ∀ x, truncated x → ∃ i ∈ patterns, consistent i x)
    (cost : ℝ) (hcost : ∀ i ∈ patterns,
      P.E (fun x => if consistent i x then f x else 0) ≤ cost) :
    P.E (fun x => if truncated x then f x else 0) ≤ (patterns.card : ℝ) * cost := by
  have hpoint : ∀ x, (if truncated x then f x else 0) ≤
      ∑ i ∈ patterns, if consistent i x then f x else 0 := by
    intro x
    by_cases ht : truncated x
    · obtain ⟨i, hi, hx⟩ := hcover x ht
      simp only [ht, ite_true]
      have h := Finset.single_le_sum (f := fun j => if consistent j x then f x else 0)
        (fun j _ => by split_ifs <;> simp [hf]) hi
      simpa [hx] using h
    · simp only [ht, ite_false]
      exact Finset.sum_nonneg (fun i _ => by split_ifs <;> simp [hf])
  calc
    P.E (fun x => if truncated x then f x else 0) ≤
        P.E (fun x => ∑ i ∈ patterns, if consistent i x then f x else 0) := by
      unfold FinLaw.E
      exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (P.nonneg x))
    _ = ∑ i ∈ patterns, P.E (fun x => if consistent i x then f x else 0) := by
      unfold FinLaw.E
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ i ∈ patterns, cost := Finset.sum_le_sum hcost
    _ = (patterns.card : ℝ) * cost := by simp

 theorem riskBoundFromReplayPatterns {Ω I : Type*} [Fintype Ω] [Fintype I]
    (P : FinLaw Ω) (gate closure : Ω → Prop) (patterns : Finset I)
    (consistent : I → Ω → Prop) (f : Ω → ℝ) (η : ℝ)
    (hη : 0 < η) (hf : ∀ x, 0 ≤ f x)
    (hcover : ∀ x, gate x ∧ ¬ closure x → ∃ i ∈ patterns, consistent i x)
    (closureCost patternCost bound : ℝ)
    (hclosure : P.pr (fun x => gate x ∧ closure x) ≤ closureCost)
    (hpattern : ∀ i ∈ patterns, P.E (fun x => if consistent i x then f x else 0) ≤ patternCost)
    (hbudget : closureCost + η⁻¹ * ((patterns.card : ℝ) * patternCost) ≤ bound) :
    P.pr (fun x => gate x ∧ η < f x) ≤ bound := by
  have he : P.E (fun x => if gate x ∧ ¬ closure x then f x else 0) ≤
      (patterns.card : ℝ) * patternCost := by
    convert patternCoverExpectation P patterns (fun x => gate x ∧ ¬ closure x)
      consistent f hf hcover patternCost hpattern using 1
    unfold FinLaw.E
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hg : gate x <;> by_cases hc : closure x <;> simp [hg, hc]
  exact (truncatedMarkov P gate closure f η hη hf).trans
    ((add_le_add hclosure (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hη.le))).trans hbudget)

end HypercubeRamsey.Lane_sol_s18_n4
