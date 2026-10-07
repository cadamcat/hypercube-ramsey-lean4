import HypercubeRamsey.S06.Steps_sol_s06_steps1

namespace HypercubeRamsey.S06.Lane_sol_s06_steps1
open Classical
open scoped BigOperators
noncomputable section

/-- Normalization recovers every original nonnegative weight after multiplication by the mass. -/
theorem normalize_mass_identity {Y : Type*} [Fintype Y] (w : Y → ℝ) (y₀ y : Y)
    (hw : ∀ y, 0 ≤ w y) : (∑ z, w z) * (normalize6 w y₀).w y = w y := by
  have hm : 0 ≤ ∑ z, w z := Finset.sum_nonneg fun z _ => hw z
  have hmax : ∀ z, max 0 (w z) = w z := fun z => max_eq_right (hw z)
  by_cases hp : 0 < ∑ z, w z
  · unfold normalize6
    simp only [hmax, dif_pos hp]
    exact mul_div_cancel₀ _ hp.ne'
  · have hz : ∑ z, w z = 0 := le_antisymm (le_of_not_gt hp) hm
    have hy : w y = 0 := by
      have hle := Finset.single_le_sum (fun z _ => hw z) (Finset.mem_univ y)
      rw [hz] at hle
      exact le_antisymm hle (hw y)
    simp [hz, hy]

/-- The low predictive-density alarm under a finite Bayesian experiment. -/
theorem bayes_alarm_bound {Y D T : Type*} [Fintype Y] [Fintype D] [Fintype T]
    (W : D → Y → ℝ) (P : D → Y → FinProb T) (R : FinProb T)
    (y₀ : Y) (a : ℝ) (ha : 0 ≤ a) (hW : ∀ d y, 0 ≤ W d y)
    (hWsum : ∑ d, ∑ y, W d y ≤ 1) :
    (∑ d, ∑ i, if (∑ y, (normalize6 (W d) y₀).w y * (P d y).w i) < a * R.w i
      then ∑ y, W d y * (P d y).w i else 0) ≤ a := by
  let mass (d : D) := ∑ y, W d y
  let pred (d : D) (i : T) := ∑ y, (normalize6 (W d) y₀).w y * (P d y).w i
  have hid (d : D) (i : T) : ∑ y, W d y * (P d y).w i = mass d * pred d i := by
    dsimp [mass, pred]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [← mul_assoc, normalize_mass_identity _ y₀ y (hW d)]
  have hpoint (d : D) (i : T) :
      (if pred d i < a * R.w i then ∑ y, W d y * (P d y).w i else 0) ≤
        a * R.w i * mass d := by
    have hm0 : 0 ≤ mass d := Finset.sum_nonneg fun y _ => hW d y
    by_cases hbad : pred d i < a * R.w i
    · rw [if_pos hbad, hid, mul_comm (mass d)]
      exact mul_le_mul_of_nonneg_right hbad.le hm0
    · simp [hbad, mul_nonneg (mul_nonneg ha (R.nonneg i)) hm0]
  calc
    _ ≤ ∑ d, ∑ i, a * R.w i * mass d :=
      Finset.sum_le_sum fun d _ => Finset.sum_le_sum fun i _ => hpoint d i
    _ = a * ∑ d, mass d := by
      simp [← Finset.sum_mul, ← Finset.mul_sum, R.sum_eq_one]
    _ ≤ a * 1 := mul_le_mul_of_nonneg_left hWsum ha
    _ = a := mul_one a


/-- Raw sequential sampling obeys the predictive alarm bound on every supported retained observation. -/
theorem bayes_experiment_bound {Y D T : Type*} [Fintype Y] [Fintype D] [Fintype T]
    (Q : FinProb Y) (O : Y → FinProb D) (P : Y → D → FinProb T) (R : FinProb T)
    (B : Y → D → T → Prop) (y₀ : Y) (a : ℝ) (ha : 0 ≤ a)
    (hB : ∀ y d i, Q.w y * (O y).w d ≠ 0 → B y d i →
      (∑ z, (normalize6 (fun z => Q.w z * (O z).w d) y₀).w z * (P z d).w i) < a * R.w i) :
    (∑ y, Q.w y * (∑ d, (O y).w d * (P y d).pr (B y d))) ≤ a := by
  classical
  let W (d : D) (y : Y) := Q.w y * (O y).w d
  let pred (d : D) (i : T) := ∑ z, (normalize6 (W d) y₀).w z * (P z d).w i
  have hW (d : D) (y : Y) : 0 ≤ W d y := mul_nonneg (Q.nonneg y) ((O y).nonneg d)
  have hsum : ∑ d, ∑ y, W d y ≤ 1 := by
    rw [Finset.sum_comm]
    dsimp [W]
    simp [← Finset.mul_sum, FinProb.sum_eq_one, Q.sum_eq_one]
  have hpt (y : Y) (d : D) (i : T) :
      (if B y d i then W d y * (P y d).w i else 0) ≤
        (if pred d i < a * R.w i then W d y * (P y d).w i else 0) := by
    by_cases hw : W d y = 0
    · simp [hw]
    · by_cases hb : B y d i
      · simp [hb, hB y d i hw hb, pred, W]
      · simp only [hb, ite_false]
        split_ifs <;> [exact mul_nonneg (hW d y) ((P y d).nonneg i); exact le_rfl]
  calc
    _ = ∑ y, ∑ d, ∑ i, if B y d i then W d y * (P y d).w i else 0 := by
      unfold FinProb.pr
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro i _
      by_cases hb : B y d i <;> simp [hb, W, mul_assoc]
    _ ≤ ∑ y, ∑ d, ∑ i, if pred d i < a * R.w i then W d y * (P y d).w i else 0 :=
      Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun d _ => Finset.sum_le_sum fun i _ => hpt y d i
    _ = ∑ d, ∑ i, if pred d i < a * R.w i then ∑ y, W d y * (P y d).w i else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hp : pred d i < a * R.w i <;> simp [hp]
    _ ≤ a := bayes_alarm_bound W (fun d y => P y d) R y₀ a ha hW hsum


/-- A uniformly capped joint likelihood gives a tail bound for the maximum posterior atom. -/
theorem joint_cap_bad_mass {Y D : Type*} [Fintype Y] [Fintype D]
    (W : D → Y → ℝ) (R : FinProb D) (y₀ : Y) (N B t : ℝ)
    (hW : ∀ d y, 0 ≤ W d y) (hB : 0 ≤ B) (ht : 0 < t)
    (hcap : ∀ d y, N * W d y ≤ B * R.w d) :
    (∑ d, if ∃ y, t < N * (normalize6 (W d) y₀).w y then ∑ y, W d y else 0) ≤ B / t := by
  classical
  have hpt (d : D) :
      (if ∃ y, t < N * (normalize6 (W d) y₀).w y then ∑ y, W d y else 0) ≤ (B / t) * R.w d := by
    by_cases hb : ∃ y, t < N * (normalize6 (W d) y₀).w y
    · rw [if_pos hb]
      have hm : 0 ≤ ∑ y, W d y := Finset.sum_nonneg fun y _ => hW d y
      by_cases hz : ∑ y, W d y = 0
      · simp [hz, mul_nonneg (div_nonneg hB ht.le) (R.nonneg d)]
      · have hp : 0 < ∑ y, W d y := lt_of_le_of_ne hm (Ne.symm hz)
        obtain ⟨y, hy⟩ := hb
        have hc := mul_lt_mul_of_pos_right hy hp
        have hid := normalize_mass_identity (W d) y₀ y (hW d)
        have hupper := hcap d y
        have hcross : t * (∑ y, W d y) < B * R.w d := by
          calc
            _ < (N * (normalize6 (W d) y₀).w y) * (∑ y, W d y) := hc
            _ = N * W d y := by rw [mul_assoc, mul_comm ((normalize6 (W d) y₀).w y), hid]
            _ ≤ B * R.w d := hupper
        have hh : (∑ y, W d y) < (B * R.w d) / t := (lt_div_iff₀ ht).2 (by nlinarith [hcross])
        have heq : (B * R.w d) / t = (B / t) * R.w d := by ring
        exact (hh.trans_eq heq).le
    · simp [hb, mul_nonneg (div_nonneg hB ht.le) (R.nonneg d)]
  calc
    _ ≤ ∑ d, (B / t) * R.w d := Finset.sum_le_sum fun d _ => hpt d
    _ = B / t := by rw [← Finset.mul_sum, R.sum_eq_one, mul_one]

theorem bayes_cap_experiment {Y D : Type*} [Fintype Y] [Fintype D]
    (Q : FinProb Y) (O : Y → FinProb D) (R : FinProb D) (y₀ : Y)
    (A : Y → D → Prop) (N B t : ℝ) (hB : 0 ≤ B) (ht : 0 < t)
    (hcap : ∀ d y, N * (Q.w y * (O y).w d) ≤ B * R.w d)
    (hA : ∀ y d, Q.w y * (O y).w d ≠ 0 → A y d →
      ∃ z, t < N * (normalize6 (fun y => Q.w y * (O y).w d) y₀).w z) :
    (∑ y, Q.w y * (O y).pr (A y)) ≤ B / t := by
  classical
  let W (d : D) (y : Y) := Q.w y * (O y).w d
  let bad (d : D) := ∃ z, t < N * (normalize6 (W d) y₀).w z
  have hW (d : D) (y : Y) : 0 ≤ W d y := mul_nonneg (Q.nonneg y) ((O y).nonneg d)
  have hpoint (y : Y) (d : D) : (if A y d then W d y else 0) ≤ (if bad d then W d y else 0) := by
    by_cases hw : W d y = 0
    · simp [hw]
    · by_cases ha : A y d
      · simp [ha, hA y d hw ha, bad, W]
      · simp only [ha, ite_false]
        split_ifs <;> [exact hW d y; exact le_rfl]
  calc
    _ = ∑ y, ∑ d, if A y d then W d y else 0 := by
      unfold FinProb.pr
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro d _
      by_cases ha : A y d <;> simp [ha, W]
    _ ≤ ∑ y, ∑ d, if bad d then W d y else 0 :=
      Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun d _ => hpoint y d
    _ = ∑ d, if bad d then ∑ y, W d y else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hb : bad d <;> simp [hb]
    _ ≤ B / t := joint_cap_bad_mass W R y₀ N B t hW hB ht hcap

end
end HypercubeRamsey.S06.Lane_sol_s06_steps1
