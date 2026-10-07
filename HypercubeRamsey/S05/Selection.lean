import HypercubeRamsey.S05.Defs

/-!
# L5.1k and the reusable selection-adjustment node

The table is defined for each candidate value separately.  `likelihood` therefore includes the integration
over every unrecorded array generated at that candidate value, as required by the finite disintegration in
the paper.
-/

namespace HypercubeRamsey

noncomputable section

/-- A finite target/data experiment with candidate-dependent presentation likelihoods (05:910–929).  Each gated
observation density integrates to at most one but the gates of different records need not be disjoint, so the
total likelihood is at most the record count `recordBound`; the presentations themselves are disjoint
(`gated_subprob`). -/
structure SelectionExperiment5 (Target Data : Type*) [Fintype Target] [Fintype Data] where
  prior : FinProb Target
  likelihood : Target → Data → ℝ
  selection : Target → Data → ℝ
  likelihood_nonneg : ∀ y d, 0 ≤ likelihood y d
  selection_nonneg : ∀ y d, 0 ≤ selection y d
  selection_le_one : ∀ y d, selection y d ≤ 1
  recordBound : ℝ
  likelihood_mass : ∀ y, ∑ d, likelihood y d ≤ recordBound
  gated_subprob : ∀ y, ∑ d, likelihood y d * selection y d ≤ 1

/-- Unadjusted predictive mass for one recorded observation. -/
def SelectionExperiment5.baseMass {Target Data : Type*} [Fintype Target] [Fintype Data]
    (X : SelectionExperiment5 Target Data) (d : Data) : ℝ :=
  ∑ y, X.prior.w y * X.likelihood y d

/-- Predictive mass after the selection event. -/
def SelectionExperiment5.selectedMass {Target Data : Type*} [Fintype Target] [Fintype Data]
    (X : SelectionExperiment5 Target Data) (d : Data) : ℝ :=
  ∑ y, X.prior.w y * X.likelihood y d * X.selection y d

/-- The posterior before correcting for the selection event. -/
def SelectionExperiment5.baseRow {Target Data : Type*} [Fintype Target] [Fintype Data]
    (X : SelectionExperiment5 Target Data) (d : Data) (y : Target) : ℝ :=
  if X.baseMass d = 0 then 0 else X.prior.w y * X.likelihood y d / X.baseMass d

/-- The posterior after correcting for the selection event. -/
def SelectionExperiment5.adjustedRow {Target Data : Type*} [Fintype Target] [Fintype Data]
    (X : SelectionExperiment5 Target Data) (d : Data) (y : Target) : ℝ :=
  if X.selectedMass d = 0 then 0 else
    X.prior.w y * X.likelihood y d * X.selection y d / X.selectedMass d

/-- The low proxy row: use the adjusted posterior when its average selection probability clears `ε`, and
fall back to the original posterior otherwise. -/
def SelectionExperiment5.proxyRow {Target Data : Type*} [Fintype Target] [Fintype Data]
    (X : SelectionExperiment5 Target Data) (ε : ℝ) (d : Data) (y : Target) : ℝ :=
  if X.baseMass d ≠ 0 ∧ ε * X.baseMass d ≤ X.selectedMass d then
    X.adjustedRow d y else X.baseRow d y

/-- F-SelAdj / L5.1k: the selected row pays at most the reciprocal selection threshold relative to the
unadjusted posterior. -/
theorem L5_1k_row_comparison {Target Data : Type*} [Fintype Target] [Fintype Data]
    (X : SelectionExperiment5 Target Data) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ d y, X.proxyRow ε d y ≤ ε⁻¹ * X.baseRow d y := by
  intro d y
  have hbaseMass : 0 ≤ X.baseMass d := by
    unfold SelectionExperiment5.baseMass
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg (X.prior.nonneg z) (X.likelihood_nonneg z d)
  have hselectedMass : 0 ≤ X.selectedMass d := by
    unfold SelectionExperiment5.selectedMass
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg (mul_nonneg (X.prior.nonneg z) (X.likelihood_nonneg z d))
      (X.selection_nonneg z d)
  have hrow_nonneg : 0 ≤ X.baseRow d y := by
    unfold SelectionExperiment5.baseRow
    split_ifs with h
    · exact le_rfl
    · exact div_nonneg (mul_nonneg (X.prior.nonneg y) (X.likelihood_nonneg y d)) hbaseMass
  by_cases hproxy : X.baseMass d ≠ 0 ∧ ε * X.baseMass d ≤ X.selectedMass d
  · rcases hproxy with ⟨hbase_ne, hthreshold⟩
    have hproxy' : X.baseMass d ≠ 0 ∧ ε * X.baseMass d ≤ X.selectedMass d :=
      ⟨hbase_ne, hthreshold⟩
    have hbase_pos : 0 < X.baseMass d := by
      by_contra h
      have hz : X.baseMass d = 0 := le_antisymm (le_of_not_gt h) hbaseMass
      exact hbase_ne hz
    have hselected_pos : 0 < X.selectedMass d :=
      lt_of_lt_of_le (mul_pos hε hbase_pos) hthreshold
    let p := X.prior.w y * X.likelihood y d
    have hp : 0 ≤ p := mul_nonneg (X.prior.nonneg y) (X.likelihood_nonneg y d)
    have hnum : p * X.selection y d ≤ p := by
      calc
        p * X.selection y d ≤ p * 1 :=
          mul_le_mul_of_nonneg_left (X.selection_le_one y d) hp
        _ = p := by ring
    calc
      X.proxyRow ε d y = X.adjustedRow d y := by
        simp [SelectionExperiment5.proxyRow, hproxy']
      _ = (p * X.selection y d) / X.selectedMass d := by
        simp [SelectionExperiment5.adjustedRow, p, ne_of_gt hselected_pos]
      _ ≤ p / X.selectedMass d := div_le_div_of_nonneg_right hnum hselected_pos.le
      _ ≤ p / (ε * X.baseMass d) :=
        div_le_div_of_nonneg_left hp (mul_pos hε hbase_pos) hthreshold
      _ = ε⁻¹ * (p / X.baseMass d) := by
        field_simp [ne_of_gt hε, ne_of_gt hbase_pos]
      _ = ε⁻¹ * X.baseRow d y := by
        simp [SelectionExperiment5.baseRow, p, hbase_ne]
  · have hinv : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1
    calc
      X.proxyRow ε d y = X.baseRow d y := by
        simp [SelectionExperiment5.proxyRow, hproxy]
      _ = 1 * X.baseRow d y := by ring
      _ ≤ ε⁻¹ * X.baseRow d y := mul_le_mul_of_nonneg_right hinv hrow_nonneg

/-- L5.1k(2) (05:975–989): the disjoint-presentation cancellation bound for the selection-adjusted proxy row; the
fallback part costs `ε` times the record count, which is at most `ε^{-1}`. -/
theorem L5_1k_mean_bound {Target Data : Type*} [Fintype Target] [Fintype Data]
    (X : SelectionExperiment5 Target Data) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hR : ε * X.recordBound ≤ 1) :
    ∀ y, ∑ d, X.selectedMass d * X.proxyRow ε d y ≤ 2 * X.prior.w y := by
  intro y
  have hprior : 0 ≤ X.prior.w y := X.prior.nonneg y
  have hbaseMass : ∀ d, 0 ≤ X.baseMass d := by
    intro d
    unfold SelectionExperiment5.baseMass
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg (X.prior.nonneg z) (X.likelihood_nonneg z d)
  have hselectedMass : ∀ d, 0 ≤ X.selectedMass d := by
    intro d
    unfold SelectionExperiment5.selectedMass
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg (mul_nonneg (X.prior.nonneg z) (X.likelihood_nonneg z d))
      (X.selection_nonneg z d)
  have hselected_le_base : ∀ d, X.selectedMass d ≤ X.baseMass d := by
    intro d
    unfold SelectionExperiment5.selectedMass SelectionExperiment5.baseMass
    apply Finset.sum_le_sum
    intro z hz
    have hp : 0 ≤ X.prior.w z * X.likelihood z d :=
      mul_nonneg (X.prior.nonneg z) (X.likelihood_nonneg z d)
    calc
      X.prior.w z * X.likelihood z d * X.selection z d ≤
          X.prior.w z * X.likelihood z d * 1 :=
        mul_le_mul_of_nonneg_left (X.selection_le_one z d) hp
      _ = X.prior.w z * X.likelihood z d := by ring
  have hpoint : ∀ d,
      X.selectedMass d * X.proxyRow ε d y ≤
        X.prior.w y * X.likelihood y d * X.selection y d +
          ε * (X.prior.w y * X.likelihood y d) := by
    intro d
    let p := X.prior.w y * X.likelihood y d
    have hp : 0 ≤ p := mul_nonneg (X.prior.nonneg y) (X.likelihood_nonneg y d)
    by_cases hproxy : X.baseMass d ≠ 0 ∧ ε * X.baseMass d ≤ X.selectedMass d
    · rcases hproxy with ⟨hbase_ne, hthreshold⟩
      have hproxy' : X.baseMass d ≠ 0 ∧ ε * X.baseMass d ≤ X.selectedMass d :=
        ⟨hbase_ne, hthreshold⟩
      have hbase_pos : 0 < X.baseMass d := by
        by_contra h
        have hz : X.baseMass d = 0 := le_antisymm (le_of_not_gt h) (hbaseMass d)
        exact hbase_ne hz
      have hselected_pos : 0 < X.selectedMass d :=
        lt_of_lt_of_le (mul_pos hε hbase_pos) hthreshold
      rw [SelectionExperiment5.proxyRow, if_pos hproxy']
      rw [SelectionExperiment5.adjustedRow, if_neg (ne_of_gt hselected_pos)]
      change X.selectedMass d * (p * X.selection y d / X.selectedMass d) ≤
        p * X.selection y d + ε * p
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hselected_pos)]
      nlinarith [mul_nonneg hε.le hp]
    · by_cases hzero : X.baseMass d = 0
      · have hselected_zero : X.selectedMass d = 0 := by
          apply le_antisymm
          · simpa [hzero] using hselected_le_base d
          · exact hselectedMass d
        rw [SelectionExperiment5.proxyRow, if_neg hproxy, hselected_zero]
        change 0 * X.baseRow d y ≤ p * X.selection y d + ε * p
        simp [SelectionExperiment5.baseRow, hzero, p]
        exact add_nonneg
          (mul_nonneg hp (X.selection_nonneg y d))
          (mul_nonneg hε.le hp)
      · have hbase_pos : 0 < X.baseMass d := by
          by_contra h
          have hz : X.baseMass d = 0 := le_antisymm (le_of_not_gt h) (hbaseMass d)
          exact hzero hz
        have hthreshold : X.selectedMass d ≤ ε * X.baseMass d := by
          by_contra h
          have hgt : ε * X.baseMass d < X.selectedMass d := lt_of_not_ge h
          exact hproxy ⟨hzero, le_of_lt hgt⟩
        have hrow : X.baseRow d y = p / X.baseMass d := by
          simp [SelectionExperiment5.baseRow, p, hzero]
        have hrow_nonneg : 0 ≤ X.baseRow d y := by
          rw [hrow]
          exact div_nonneg hp hbase_pos.le
        have hlow : X.selectedMass d * X.baseRow d y ≤ ε * p := by
          rw [hrow]
          calc
            X.selectedMass d * (p / X.baseMass d) ≤
                (ε * X.baseMass d) * (p / X.baseMass d) :=
              mul_le_mul_of_nonneg_right hthreshold (div_nonneg hp hbase_pos.le)
            _ = ε * p := by
              field_simp [ne_of_gt hbase_pos]
        rw [SelectionExperiment5.proxyRow, if_neg hproxy]
        change X.selectedMass d * X.baseRow d y ≤ p * X.selection y d + ε * p
        have hgate : 0 ≤ p * X.selection y d := mul_nonneg hp (X.selection_nonneg y d)
        nlinarith
  have hgate_sum :
      (∑ d, X.prior.w y * X.likelihood y d * X.selection y d) ≤ X.prior.w y := by
    calc
      (∑ d, X.prior.w y * X.likelihood y d * X.selection y d) =
          X.prior.w y * (∑ d, X.likelihood y d * X.selection y d) := by
        calc
          (∑ d, X.prior.w y * X.likelihood y d * X.selection y d) =
              ∑ d, X.prior.w y * (X.likelihood y d * X.selection y d) := by
            apply Finset.sum_congr rfl
            intro d hd
            ring
          _ = X.prior.w y * (∑ d, X.likelihood y d * X.selection y d) := by
            rw [← Finset.mul_sum]
      _ ≤ X.prior.w y * 1 := mul_le_mul_of_nonneg_left (X.gated_subprob y) hprior
      _ = X.prior.w y := by ring
  have hbase_sum :
      (∑ d, X.prior.w y * X.likelihood y d) ≤ X.prior.w y * X.recordBound := by
    calc
      (∑ d, X.prior.w y * X.likelihood y d) =
          X.prior.w y * (∑ d, X.likelihood y d) := by rw [← Finset.mul_sum]
      _ ≤ X.prior.w y * X.recordBound := mul_le_mul_of_nonneg_left (X.likelihood_mass y) hprior
  calc
    (∑ d, X.selectedMass d * X.proxyRow ε d y) ≤
        ∑ d, (X.prior.w y * X.likelihood y d * X.selection y d +
          ε * (X.prior.w y * X.likelihood y d)) :=
      Finset.sum_le_sum fun d hd => hpoint d
    _ = (∑ d, X.prior.w y * X.likelihood y d * X.selection y d) +
          ε * (∑ d, X.prior.w y * X.likelihood y d) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ X.prior.w y + ε * (X.prior.w y * X.recordBound) := by
      exact add_le_add hgate_sum (mul_le_mul_of_nonneg_left hbase_sum hε.le)
    _ ≤ 2 * X.prior.w y := by
      nlinarith [mul_le_mul_of_nonneg_left hR hprior]

end
end HypercubeRamsey
