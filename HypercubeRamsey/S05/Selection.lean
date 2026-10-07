import HypercubeRamsey.S05.Records

/-!
# L5.1k and the reusable selection-adjustment node

The table is defined for each candidate value separately.  `likelihood` therefore includes the integration
over every unrecorded array generated at that candidate value, as required by the finite disintegration in
the paper.
-/

namespace HypercubeRamsey

noncomputable section

/-- A finite target/data experiment with candidate-dependent presentation likelihoods. -/
structure SelectionExperiment5 (Target Data : Type*) [Fintype Target] [Fintype Data] where
  prior : FinProb Target
  likelihood : Target → Data → ℝ
  selection : Target → Data → ℝ
  likelihood_nonneg : ∀ y d, 0 ≤ likelihood y d
  selection_nonneg : ∀ y d, 0 ≤ selection y d
  selection_le_one : ∀ y d, selection y d ≤ 1
  likelihood_subprob : ∀ y, ∑ d, likelihood y d ≤ 1
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
  sorry

/-- The disjoint-presentation cancellation bound for the selection-adjusted proxy row. -/
theorem L5_1k_mean_bound {Target Data : Type*} [Fintype Target] [Fintype Data]
    (X : SelectionExperiment5 Target Data) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ y, ∑ d, X.selectedMass d * X.proxyRow ε d y ≤ 2 * X.prior.w y := by
  sorry

end
end HypercubeRamsey
