import HypercubeRamsey.S05.History_sol_s05_hist1f_apply

namespace HypercubeRamsey.Lane_sol_s05_hist1b

open Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000

/-- The negative-log likelihood has exponential moment at parameter one half
at most two, for arbitrary finite laws, including zero-weight atoms. -/
theorem finite_negative_log_moment {Ω : Type*} [Fintype Ω] (P Q : FinProb Ω) :
    P.expect (fun y => Real.exp (max 0 (Real.log (Q.w y / P.w y)) / 2)) ≤ 2 := by
  let r (y : Ω) := P.w y * Real.exp (max 0 (Real.log (Q.w y / P.w y)) / 2)
  have hsq (y : Ω) : r y ^ 2 ≤ P.w y * (P.w y + Q.w y) := by
    by_cases hp : P.w y = 0
    · simp [r, hp]
    have hp0 : 0 < P.w y := lt_of_le_of_ne (P.nonneg y) (Ne.symm hp)
    by_cases hl : Real.log (Q.w y / P.w y) ≤ 0
    · simp only [r, max_eq_left hl, zero_div, Real.exp_zero, mul_one]
      nlinarith [mul_nonneg (P.nonneg y) (Q.nonneg y)]
    · have hl0 : 0 < Real.log (Q.w y / P.w y) := lt_of_not_ge hl
      have hq : Q.w y ≠ 0 := by intro hz; simp [hz] at hl0
      have hq0 : 0 < Q.w y := lt_of_le_of_ne (Q.nonneg y) (Ne.symm hq)
      have he : Real.exp (Real.log (Q.w y / P.w y) / 2) ^ 2 = Q.w y / P.w y := by
        rw [← Real.exp_nat_mul]
        norm_num only [Nat.cast_ofNat]
        rw [show 2 * (Real.log (Q.w y / P.w y) / 2) = Real.log (Q.w y / P.w y) by ring]
        exact Real.exp_log (div_pos hq0 hp0)
      have hr : r y ^ 2 = P.w y * Q.w y := by
        simp only [r, max_eq_right hl0.le, mul_pow, he]
        field_simp [hp]
      rw [hr]
      nlinarith [sq_nonneg (P.w y)]
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun y _ => P.nonneg y) (fun y _ => add_nonneg (P.nonneg y) (Q.nonneg y))
    (fun y _ => hsq y)
  rw [P.sum_eq_one, Finset.sum_add_distrib, P.sum_eq_one, Q.sum_eq_one] at hc
  change (P.expect (fun y => Real.exp (max 0 (Real.log (Q.w y / P.w y)) / 2))) ^ 2 ≤ 1 * (1 + 1) at hc
  nlinarith

/-- Restrict to density-good atoms of bounded cost. A clipped expectation and
an exceptional density mass suffice for a capped supported law and its true cost. -/
theorem finite_density_cost_restriction {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FinProb Ω) (f : Ω → ℝ) (D L B η β : ℝ)
    (hf : ∀ ω, 0 ≤ f ω) (hD : 0 ≤ D) (hL : 0 < L) (hB : 0 ≤ B)
    (hη : 0 ≤ η) (hβ : η + B / L ≤ β) (hβ1 : β < 1)
    (hdensity : P.pr (fun ω => D < P.w ω) ≤ η)
    (hclip : P.expect (fun ω => min L (f ω)) ≤ B) :
    ∃ R : FinProb Ω,
      (∀ ω, R.w ω ≤ D / (1 - β)) ∧
      (∀ ω, R.w ω ≠ 0 → P.w ω ≠ 0) ∧ R.expect f ≤ B / (1 - β) := by
  classical
  let G (ω : Ω) : Prop := P.w ω ≤ D ∧ f ω ≤ L
  let badCost (ω : Ω) : Prop := L < f ω
  have hcost : P.pr badCost ≤ B / L := by
    have hc := P.markov (fun ω => min L (f ω)) L (fun ω => le_min hL.le (hf ω)) hL
    have hm : P.pr badCost ≤ P.pr (fun ω => L ≤ min L (f ω)) := by
      unfold FinProb.pr
      apply Finset.sum_le_sum
      intro ω _
      by_cases h : badCost ω
      · have hh : L ≤ min L (f ω) := le_min (le_refl _) h.le
        simp only [if_pos h, if_pos hh]
        exact le_refl _
      · simp only [if_neg h]
        split_ifs <;> simp [P.nonneg ω]
    exact hm.trans (hc.trans (div_le_div_of_nonneg_right hclip hL.le))
  have hbad : P.pr (fun ω => ¬ G ω) ≤ β := by
    have he : (fun ω => ¬ G ω) = (fun ω => D < P.w ω ∨ badCost ω) := by
      funext ω
      apply propext
      exact not_and_or.trans (or_congr not_le not_le)
    rw [he]
    exact (P.pr_union _ _).trans ((add_le_add hdensity hcost).trans hβ)
  have hsum : P.pr G + P.pr (fun ω => ¬ G ω) = 1 := by
    unfold FinProb.pr
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ ω, P.w ω := by
        apply Finset.sum_congr rfl
        intro ω _
        by_cases h : G ω <;> simp [h]
      _ = 1 := P.sum_eq_one
  have hmass : 1 - β ≤ P.pr G := by linarith
  have hpos : 0 < P.pr G := lt_of_lt_of_le (by linarith) hmass
  have hweight : (∑ ω, if G ω then P.w ω else 0) = P.pr G := by
    unfold FinProb.pr
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : G ω <;> simp only [h, ite_true, ite_false]
  let R : FinProb Ω := {
    w := fun ω => (if G ω then P.w ω else 0) / P.pr G
    nonneg := by
      intro ω
      apply div_nonneg _ hpos.le
      split_ifs <;> simp [P.nonneg ω]
    sum_eq_one := by
      rw [← Finset.sum_div, hweight]
      exact div_self hpos.ne' }

  refine ⟨R, ?_, ?_, ?_⟩
  · intro ω
    dsimp only [R]
    by_cases h : G ω
    · rw [if_pos h]
      exact div_le_div₀ hD (h.1) (by linarith) hmass
    · rw [if_neg h, zero_div]
      exact div_nonneg hD (by linarith)
  · intro ω hω hz
    apply hω
    dsimp only [R]
    by_cases h : G ω <;> simp only [h, ite_true, ite_false, hz, zero_div]
  · have hnum : ∑ ω, (if G ω then P.w ω else 0) * f ω ≤ B := by
      apply le_trans _ hclip
      unfold FinProb.expect
      apply Finset.sum_le_sum
      intro ω _
      by_cases h : G ω
      · simp only [if_pos h, min_eq_right h.2]
        exact le_refl _
      · rw [if_neg h, zero_mul]
        exact mul_nonneg (P.nonneg ω) (le_min hL.le (hf ω))
    unfold FinProb.expect
    dsimp only [R]
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    exact (div_le_div_of_nonneg_right hnum hpos.le).trans
      (div_le_div_of_nonneg_left hB (by linarith) hmass)

/-- Rounding a price vector upward gives a finite integer direction that
pointwise dominates it after one fixed normalization loss. -/
theorem finite_price_rounding {I : Type*} [Fintype I] [Nonempty I]
    (P : FinProb I) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : I → ℕ, (0 < ∑ i, a i) ∧
      ((∑ i, a i : ℕ) : ℝ) ≤ (1 + ε⁻¹) * Fintype.card I ∧
      ∀ i, P.w i ≤ (1 + ε) * ((a i : ℝ) / (∑ j, a j : ℕ)) := by
  let r : ℝ := Fintype.card I
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card I)
  let a (i : I) := ⌈r * P.w i / ε⌉₊
  let A : ℕ := ∑ i, a i
  have hlo (i : I) : r * P.w i / ε ≤ (a i : ℝ) := Nat.le_ceil _
  have hhi (i : I) : (a i : ℝ) ≤ r * P.w i / ε + 1 :=
    (Nat.ceil_lt_add_one (div_nonneg (mul_nonneg hr.le (P.nonneg i)) hε.le)).le
  have hsumlo : r / ε ≤ (A : ℝ) := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hlo i)
    simpa only [A, Nat.cast_sum, ← Finset.sum_div, ← Finset.mul_sum, P.sum_eq_one, mul_one] using hh
  have hsumhi : (A : ℝ) ≤ (1 + ε⁻¹) * r := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hhi i)
    simp only [← Nat.cast_sum, A, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum,
      P.sum_eq_one, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hh
    exact hh.trans_eq (by dsimp [r]; ring)
  have hA : 0 < (A : ℝ) := lt_of_lt_of_le (div_pos hr hε) hsumlo
  refine ⟨a, by exact_mod_cast hA, hsumhi, ?_⟩
  intro i
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hA).mpr
  have hi := (div_le_iff₀ hε).mp (hlo i)
  have hratio : (A : ℝ) * ε ≤ (1 + ε) * r := by
    have hh := mul_le_mul_of_nonneg_right hsumhi hε.le
    have heq : (1 + ε⁻¹) * r * ε = (1 + ε) * r := by field_simp; ring
    exact hh.trans_eq heq
  have hh1 := mul_le_mul_of_nonneg_right hi hA.le
  have hh2 := mul_le_mul_of_nonneg_right hratio (Nat.cast_nonneg (a i))
  have hh : r * (P.w i * A) ≤ r * ((1 + ε) * a i) := by nlinarith
  simpa only [mul_div_assoc] using (mul_le_mul_iff_right₀ hr).mp hh

/-- A bounded integer-direction grid has an explicit finite box count. -/
theorem finite_direction_box_card {I : Type*} [Fintype I] [DecidableEq I] (M : ℕ) :
    (Finset.univ.filter (fun a : I → Fin (M + 1) => 0 < ∑ i, (a i).val)).card ≤
      (M + 1) ^ Fintype.card I := by
  exact (Finset.card_filter_le _ _).trans_eq (by simp [Fintype.card_fun])

/-- Normalizing a restricted law increases any positive log cost by at most
its log normalization factor. -/
theorem positive_log_ratio_domination (r p q C : ℝ) (hr : 0 ≤ r) (hp : 0 ≤ p)
    (hq : 0 < q) (hC : 1 ≤ C) (hdom : r ≤ C * p) :
    max 0 (Real.log (r / q)) ≤ max 0 (Real.log (p / q)) + Real.log C := by
  have hClog : 0 ≤ Real.log C := Real.log_nonneg hC
  by_cases hr0 : r = 0
  · simp only [hr0, zero_div, Real.log_zero, max_self]
    exact add_nonneg (le_max_left _ _) hClog
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hppos : 0 < p := by
    by_contra hn
    have hz := le_antisymm (le_of_not_gt hn) hp
    rw [hz, mul_zero] at hdom
    exact (not_le_of_gt hrpos) hdom
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hlog : Real.log (r / q) ≤ Real.log (p / q) + Real.log C := by
    have hh := Real.log_le_log (div_pos hrpos hq) (div_le_div_of_nonneg_right hdom hq.le)
    rw [show C * p / q = (p / q) * C by ring, Real.log_mul (div_ne_zero hppos.ne' hq.ne') hCpos.ne'] at hh
    exact hh
  exact max_le (add_nonneg (le_max_left _ _) hClog)
    (by
      have hh : Real.log (p / q) ≤ max 0 (Real.log (p / q)) := le_max_right _ _
      linarith)

/-- The log normalization loss also bounds expected deletion costs under the
restricted law, with the reference fixed. -/
theorem finite_log_cost_selection {Ω : Type*} [Fintype Ω]
    (P R Q : FinProb Ω) (C : ℝ) (hC : 1 ≤ C)
    (hQ : ∀ ω, 0 < Q.w ω) (hdom : ∀ ω, R.w ω ≤ C * P.w ω) :
    R.expect (fun ω => max 0 (Real.log (R.w ω / Q.w ω))) ≤
      R.expect (fun ω => max 0 (Real.log (P.w ω / Q.w ω))) + Real.log C := by
  calc
    _ ≤ R.expect (fun ω => max 0 (Real.log (P.w ω / Q.w ω)) + Real.log C) :=
      R.expect_mono (fun ω => positive_log_ratio_domination _ _ _ _ (R.nonneg ω) (P.nonneg ω) (hQ ω) hC (hdom ω))
    _ = _ := by rw [FinProb.expect_add, FinProb.expect_const]

end
end HypercubeRamsey.Lane_sol_s05_hist1b
