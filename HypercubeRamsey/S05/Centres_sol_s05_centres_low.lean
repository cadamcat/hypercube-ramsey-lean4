import HypercubeRamsey.S05.Centres_sol_s05_centres_records

namespace HypercubeRamsey.Lane_sol_s05_centres

open Classical
open scoped BigOperators
set_option maxHeartbeats 400000
noncomputable section

variable {Target Data : Type*} [Fintype Target] [Fintype Data]

theorem selection_baseMass_nonneg (X : SelectionExperiment5 Target Data) (d : Data) :
    0 ≤ X.baseMass d := Finset.sum_nonneg fun y _ =>
  mul_nonneg (X.prior.nonneg y) (X.likelihood_nonneg y d)

theorem selection_selectedMass_nonneg (X : SelectionExperiment5 Target Data) (d : Data) :
    0 ≤ X.selectedMass d := Finset.sum_nonneg fun y _ =>
  mul_nonneg (mul_nonneg (X.prior.nonneg y) (X.likelihood_nonneg y d)) (X.selection_nonneg y d)

theorem selection_proxy_nonneg (X : SelectionExperiment5 Target Data) (ε : ℝ) (d : Data) (y : Target) :
    0 ≤ X.proxyRow ε d y := by
  classical
  unfold SelectionExperiment5.proxyRow
  split_ifs
  · unfold SelectionExperiment5.adjustedRow
    split_ifs
    · exact le_rfl
    · exact div_nonneg
        (mul_nonneg (mul_nonneg (X.prior.nonneg y) (X.likelihood_nonneg y d)) (X.selection_nonneg y d))
        (selection_selectedMass_nonneg X d)
  · unfold SelectionExperiment5.baseRow
    split_ifs
    · exact le_rfl
    · exact div_nonneg (mul_nonneg (X.prior.nonneg y) (X.likelihood_nonneg y d))
        (selection_baseMass_nonneg X d)

theorem selection_proxy_sum (X : SelectionExperiment5 Target Data) (ε : ℝ) (hε : 0 < ε)
    (d : Data) (hd : 0 < X.baseMass d) : ∑ y, X.proxyRow ε d y = 1 := by
  classical
  by_cases hg : X.baseMass d ≠ 0 ∧ ε * X.baseMass d ≤ X.selectedMass d
  · have hs : 0 < X.selectedMass d := (mul_pos hε hd).trans_le hg.2
    simp only [SelectionExperiment5.proxyRow, if_pos hg, SelectionExperiment5.adjustedRow,
      if_neg hs.ne']
    rw [← Finset.sum_div]
    change X.selectedMass d / X.selectedMass d = 1
    exact div_self hs.ne'
  · simp only [SelectionExperiment5.proxyRow, if_neg hg, SelectionExperiment5.baseRow,
      if_neg hd.ne']
    rw [← Finset.sum_div]
    change X.baseMass d / X.baseMass d = 1
    exact div_self hd.ne'

def selectionProxyLaw (X : SelectionExperiment5 Target Data) (ε : ℝ) (hε : 0 < ε)
    (d : Data) (hd : 0 < X.baseMass d) : FinProb Target where
  w := X.proxyRow ε d
  nonneg := selection_proxy_nonneg X ε d
  sum_eq_one := selection_proxy_sum X ε hε d hd

theorem selection_proxy_support (X : SelectionExperiment5 Target Data) (ε : ℝ)
    (d : Data) (y : Target) (hy : X.proxyRow ε d y ≠ 0) :
    X.prior.w y ≠ 0 ∧ X.likelihood y d ≠ 0 := by
  classical
  by_cases hg : X.baseMass d ≠ 0 ∧ ε * X.baseMass d ≤ X.selectedMass d
  · rw [SelectionExperiment5.proxyRow, if_pos hg] at hy
    by_cases hs : X.selectedMass d = 0
    · simp [SelectionExperiment5.adjustedRow, hs] at hy
    · simp only [SelectionExperiment5.adjustedRow, if_neg hs] at hy
      have hn := (mul_ne_zero_iff.mp (div_ne_zero_iff.mp hy).1).1
      exact mul_ne_zero_iff.mp hn
  · rw [SelectionExperiment5.proxyRow, if_neg hg] at hy
    by_cases hs : X.baseMass d = 0
    · simp [SelectionExperiment5.baseRow, hs] at hy
    · simp only [SelectionExperiment5.baseRow, if_neg hs] at hy
      exact mul_ne_zero_iff.mp (div_ne_zero_iff.mp hy).1

def lowIndexRow {N : ℕ} (R : Law N) (t : ℕ) (o : Fin (t + 1) × Fin N) : ℝ :=
  if (o.1 : ℕ) = 0 then R.w o.2 else 0

theorem lowIndexRow_sum {N : ℕ} (R : Law N) (t : ℕ) :
    ∑ o : Fin (t + 1) × Fin N, lowIndexRow R t o = 1 := by
  classical
  rw [Fintype.sum_prod_type]
  have hs : (∑ i : Fin (t + 1), ∑ y : Fin N, lowIndexRow R t (i, y)) =
      ∑ y : Fin N, R.w y := by
    apply Finset.sum_eq_single 0
    · intro i _ hi
      have hv : (i : ℕ) ≠ 0 := by intro h; exact hi (Fin.ext h)
      simp [lowIndexRow, hv]
    · simp
  exact hs.trans R.sum_eq_one

end
end HypercubeRamsey.Lane_sol_s05_centres
