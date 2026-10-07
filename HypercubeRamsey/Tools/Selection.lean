import HypercubeRamsey.Framework.FinProb

/-!
# Selection-adjusted posterior

Finite form of F-SelAdj. It includes both the rowwise domination after a successful presentation gate and the
aggregate prior bound that pays at most `ε` for each record whose gate is small.
-/

namespace HypercubeRamsey

open scoped BigOperators

/-- F-SelAdj: select the presentation-weighted posterior when its mass is at least `ε` times the raw mass,
and otherwise use the raw posterior. The resulting rows have a controlled aggregate under the presented law. -/
theorem selectionAdjustedPosterior
    {Candidate Records Outcome : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Records] [DecidableEq Records] [Fintype Outcome] [DecidableEq Outcome]
    (π : FinProb Candidate) (Q : Records → FinProb Outcome)
    (F a : Records → Candidate → Outcome → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hF : ∀ r ξ o, 0 ≤ F r ξ o)
    (ha : ∀ r ξ o, 0 ≤ a r ξ o ∧ a r ξ o ≤ 1)
    (hrecord : ∀ r ξ, ∑ o, F r ξ o * (Q r).w o ≤ 1)
    (hpresentation : ∀ ξ, ∑ r, ∑ o, F r ξ o * a r ξ o * (Q r).w o ≤ 1) :
    let M : Records → Outcome → ℝ := fun r o => ∑ ξ, π.w ξ * F r ξ o
    let Ma : Records → Outcome → ℝ := fun r o => ∑ ξ, π.w ξ * F r ξ o * a r ξ o
    ∃ p : Records → Outcome → FinProb Candidate,
      (∀ r o ξ,
        (if 0 < M r o ∧ ε * M r o ≤ Ma r o then
          (p r o).w ξ = π.w ξ * F r ξ o * a r ξ o / Ma r o
        else if 0 < M r o then
          (p r o).w ξ = π.w ξ * F r ξ o / M r o
        else (p r o).w ξ = π.w ξ)) ∧
      (∀ r o ξ, 0 < M r o ∧ ε * M r o ≤ Ma r o →
        (p r o).w ξ ≤ ε⁻¹ * (π.w ξ * F r ξ o / M r o)) ∧
      (∀ ξ, ∑ r, ∑ o, Ma r o * (Q r).w o * (p r o).w ξ ≤
        (1 + ε * Fintype.card Records) * π.w ξ) := by
  classical
  sorry

end HypercubeRamsey
