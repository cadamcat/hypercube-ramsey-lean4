import HypercubeRamsey.S05.History_q_s05_hist1b

namespace HypercubeRamsey.Lane_sol_s05_hist1b

open Classical
open scoped BigOperators
noncomputable section

/-- A bounded evidence likelihood gives a uniform posterior-threshold exception bound.
The zero evidence normalizer contributes no mass, regardless of its fallback posterior. -/
theorem finite_bayes_threshold {Ω Ξ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Ξ]
    (P : FinProb Ω) (K : Ω → FinProb Ξ) (Q : FinProb Ξ) (ω₀ : Ω)
    (T : Ω → ℝ) (A C : ℝ) (hT : ∀ ω, 0 ≤ T ω) (hA : 0 ≤ A) (hC : 0 < C)
    (hbound : ∀ ω z, P.w ω * (K ω).w z ≤ A * T ω * Q.w z) :
    (FinProb.bind P K).pr (fun ωz => ∃ ω,
      C * T ω < (normalize5 (fun x => P.w x * (K x).w ωz.2) ω₀).w ω) ≤ A / C := by
  let m : Ξ → ℝ := fun z => ∑ ω, P.w ω * (K ω).w z
  let bad : Ξ → Prop := fun z => ∃ ω,
    C * T ω < (normalize5 (fun x => P.w x * (K x).w z) ω₀).w ω
  have hm (z : Ξ) : 0 ≤ m z :=
    Finset.sum_nonneg fun ω _ => mul_nonneg (P.nonneg ω) ((K ω).nonneg z)
  have hpoint (z : Ξ) : (if bad z then m z else 0) ≤ (A / C) * Q.w z := by
    by_cases hb : bad z
    · simp only [if_pos hb]
      by_cases hz : m z = 0
      · rw [hz]
        exact mul_nonneg (div_nonneg hA hC.le) (Q.nonneg z)
      have hmpos : 0 < m z := lt_of_le_of_ne (hm z) (Ne.symm hz)
      obtain ⟨ω, hω⟩ := hb
      rw [Lane_q_s05_hist1b.normalize5_weight_eq_div_of_nonneg
        (fun x => P.w x * (K x).w z) ω₀ ω
        (fun x => mul_nonneg (P.nonneg x) ((K x).nonneg z)) hmpos] at hω
      have hineq : C * T ω * m z < P.w ω * (K ω).w z :=
        (lt_div_iff₀ hmpos).mp hω
      have hTpos : 0 < T ω := by
        by_contra hnot
        have hzero : T ω = 0 := le_antisymm (le_of_not_gt hnot) (hT ω)
        have hcap := hbound ω z
        rw [hzero] at hineq hcap
        simp only [mul_zero, zero_mul] at hineq hcap
        exact (not_lt_of_ge hcap) hineq
      have hmass : C * m z < A * Q.w z :=
        (mul_lt_mul_iff_right₀ hTpos).mp (calc
          T ω * (C * m z) = C * T ω * m z := by ring
          _ < P.w ω * (K ω).w z := hineq
          _ ≤ A * T ω * Q.w z := hbound ω z
          _ = T ω * (A * Q.w z) := by ring)
      have hlt : m z < (A * Q.w z) / C :=
        (lt_div_iff₀ hC).mpr (by simpa [mul_comm] using hmass)
      exact le_of_lt (by simpa [div_mul_eq_mul_div] using hlt)
    · simp only [if_neg hb]
      exact mul_nonneg (div_nonneg hA hC.le) (Q.nonneg z)
  have heq : (FinProb.bind P K).pr (fun ωz => ∃ ω,
      C * T ω < (normalize5 (fun x => P.w x * (K x).w ωz.2) ω₀).w ω) =
      ∑ z, if bad z then m z else 0 := by
    unfold FinProb.pr
    simp only [FinProb.bind]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hb : bad z <;> simp only [bad] at hb ⊢ <;> simp [hb, m]

  rw [heq]
  calc
    _ ≤ ∑ z, (A / C) * Q.w z := Finset.sum_le_sum fun z _ => hpoint z
    _ = A / C := by rw [← Finset.mul_sum, Q.sum_eq_one, mul_one]

/-- The Step 1 comparison is the posterior-threshold estimate with the prior itself as threshold. -/
theorem finite_bayes_comparison {Ω Ξ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Ξ]
    (P : FinProb Ω) (K : Ω → FinProb Ξ) (Q : FinProb Ξ) (ω₀ : Ω)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 < C)
    (hbound : ∀ ω z, P.w ω * (K ω).w z ≤ A * P.w ω * Q.w z) :
    (FinProb.bind P K).pr (fun ωz => ∃ ω,
      C * P.w ω < (normalize5 (fun x => P.w x * (K x).w ωz.2) ω₀).w ω) ≤ A / C :=
  finite_bayes_threshold P K Q ω₀ P.w A C P.nonneg hA hC hbound

/-- The prior-cap exception is the same estimate with a constant atom threshold. -/
theorem finite_bayes_atom_cap {Ω Ξ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Ξ]
    (P : FinProb Ω) (K : Ω → FinProb Ξ) (Q : FinProb Ξ) (ω₀ : Ω)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 < C)
    (hbound : ∀ ω z, P.w ω * (K ω).w z ≤ A * Q.w z) :
    (FinProb.bind P K).pr (fun ωz => ∃ ω,
      C < (normalize5 (fun x => P.w x * (K x).w ωz.2) ω₀).w ω) ≤ A / C := by
  simpa only [mul_one] using
    finite_bayes_threshold P K Q ω₀ (fun _ => 1) A C (fun _ => by norm_num) hA hC
      (fun ω z => by simpa only [mul_one] using hbound ω z)

end
end HypercubeRamsey.Lane_sol_s05_hist1b
