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

/-- Integrate a prefix comparison over retained observations, including zero-mass histories. -/
theorem finite_bayes_retained_comparison {Ω Δ Ξ : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype Δ] [Fintype Ξ]
    (P : FinProb Ω) (K : Ω → FinProb Δ) (J : Ω → Δ → FinProb Ξ)
    (Q : Δ → FinProb Ξ) (ω₀ : Ω) (A C : ℝ) (hA : 0 ≤ A) (hC : 0 < C)
    (hbound : ∀ ω d z, (J ω d).w z ≤ A * (Q d).w z) :
    (FinProb.bind P fun ω => FinProb.bind (K ω) (J ω)).pr
      (fun x => ∃ ω,
        C * (normalize5 (fun u => P.w u * (K u).w x.2.1) ω₀).w ω <
          (normalize5 (fun u => P.w u * (K u).w x.2.1 * (J u x.2.1).w x.2.2) ω₀).w ω)
      ≤ A / C := by
  classical
  let D (d : Δ) (ω : Ω) := P.w ω * (K ω).w d
  let F (d : Δ) (z : Ξ) (ω : Ω) := D d ω * (J ω d).w z
  let md (d : Δ) := ∑ ω, D d ω
  let mf (d : Δ) (z : Ξ) := ∑ ω, F d z ω
  let bad (d : Δ) (z : Ξ) : Prop := ∃ ω,
    C * (normalize5 (D d) ω₀).w ω < (normalize5 (F d z) ω₀).w ω
  have hD (d : Δ) (ω : Ω) : 0 ≤ D d ω := mul_nonneg (P.nonneg ω) ((K ω).nonneg d)
  have hF (d : Δ) (z : Ξ) (ω : Ω) : 0 ≤ F d z ω :=
    mul_nonneg (hD d ω) ((J ω d).nonneg z)
  have hmd (d : Δ) : 0 ≤ md d := Finset.sum_nonneg fun ω _ => hD d ω
  have hmf (d : Δ) (z : Ξ) : 0 ≤ mf d z := Finset.sum_nonneg fun ω _ => hF d z ω
  have hpoint (d : Δ) (z : Ξ) :
      (if bad d z then mf d z else 0) ≤ (A / C) * md d * (Q d).w z := by
    by_cases hb : bad d z
    · simp only [if_pos hb]
      by_cases hfzero : mf d z = 0
      · rw [hfzero]
        exact mul_nonneg (mul_nonneg (div_nonneg hA hC.le) (hmd d)) ((Q d).nonneg z)
      have hfpos : 0 < mf d z := lt_of_le_of_ne (hmf d z) (Ne.symm hfzero)
      have hdpos : 0 < md d := by
        by_contra hn
        have hd0 : md d = 0 := le_antisymm (le_of_not_gt hn) (hmd d)
        have hDz (ω : Ω) : D d ω = 0 := by
          have hle := Finset.single_le_sum (fun u _ => hD d u) (Finset.mem_univ ω)
          change D d ω ≤ md d at hle
          rw [hd0] at hle
          exact le_antisymm hle (hD d ω)
        have : mf d z = 0 := by simp [mf, F, hDz]
        exact hfzero this
      obtain ⟨ω, hω⟩ := hb
      rw [Lane_q_s05_hist1b.normalize5_weight_eq_div_of_nonneg (D d) ω₀ ω (hD d) hdpos,
        Lane_q_s05_hist1b.normalize5_weight_eq_div_of_nonneg (F d z) ω₀ ω (hF d z) hfpos] at hω
      have hwpos : 0 < D d ω := by
        by_contra hn
        have hz : D d ω = 0 := le_antisymm (le_of_not_gt hn) (hD d ω)
        simp [F, hz] at hω
      have hineq : C * mf d z < (J ω d).w z * md d := by
        have hcross := (div_lt_div_iff₀ hdpos hfpos).mp
          (show (C * D d ω) / md d < F d z ω / mf d z by simpa [mul_div_assoc] using hω)
        apply (mul_lt_mul_iff_right₀ hwpos).mp
        calc
          D d ω * (C * mf d z) = C * D d ω * mf d z := by ring
          _ < F d z ω * md d := hcross
          _ = D d ω * ((J ω d).w z * md d) := by dsimp [F]; ring
      have hmass : C * mf d z ≤ A * (Q d).w z * md d :=
        hineq.le.trans (mul_le_mul_of_nonneg_right (hbound ω d z) (hmd d))
      have hdiv := (le_div_iff₀ hC).mpr (show mf d z * C ≤ A * (Q d).w z * md d by
        simpa [mul_comm] using hmass)
      exact hdiv.trans_eq (by ring)
    · simp only [if_neg hb]
      exact mul_nonneg (mul_nonneg (div_nonneg hA hC.le) (hmd d)) ((Q d).nonneg z)
  have htotal : ∑ d, md d = 1 := by
    simp only [md, D]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, FinProb.sum_eq_one, mul_one]
    exact P.sum_eq_one
  have heq : (FinProb.bind P fun ω => FinProb.bind (K ω) (J ω)).pr
      (fun x => ∃ ω,
        C * (normalize5 (fun u => P.w u * (K u).w x.2.1) ω₀).w ω <
          (normalize5 (fun u => P.w u * (K u).w x.2.1 * (J u x.2.1).w x.2.2) ω₀).w ω) =
      ∑ d, ∑ z, if bad d z then mf d z else 0 := by
    unfold FinProb.pr
    simp only [FinProb.bind]
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hb : bad d z
    · simp only [bad, D, F] at hb
      simp [bad, D, F, mf, hb, mul_assoc]
    · simp only [bad, D, F] at hb
      simp [bad, D, F, hb]
  rw [heq]
  calc
    _ ≤ ∑ d, ∑ z, (A / C) * md d * (Q d).w z :=
      Finset.sum_le_sum fun d _ => Finset.sum_le_sum fun z _ => hpoint d z
    _ = A / C := by
      simp_rw [← Finset.mul_sum, FinProb.sum_eq_one, mul_one]
      rw [← Finset.mul_sum, htotal, mul_one]

end
end HypercubeRamsey.Lane_sol_s05_hist1b
