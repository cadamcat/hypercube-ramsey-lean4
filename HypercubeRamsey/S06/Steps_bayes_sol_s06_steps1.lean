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

end
end HypercubeRamsey.S06.Lane_sol_s06_steps1
