import HypercubeRamsey.S05.Defs

/-!
# Shared tool request

The main framework has no Section 3.8 local height-selection module yet.  This is the position-averaged,
legal-eligibility form Section 5 needs for its forced-center selection estimate; the Section 6 lane can use
the same predicate with its changed height rule.
-/

namespace HypercubeRamsey

open Classical
open scoped BigOperators

/-- SHARED: L3.8. The position-averaged supremum form of the forced-center bound over every legal
pre-activation eligibility choice. -/
def PositionAveragedForcedCenterBound5
    {Position Eligibility Centre : Type*}
    [Fintype Position] [Fintype Eligibility] [Fintype Centre]
    (positionLaw : FinProb Position)
    (legalEligibility : Position → Finset Eligibility)
    (forcedSelectionProbability : Position → Eligibility → Centre → ℝ)
    (lambda : ℝ) : Prop :=
  ∀ choice : ∀ p, {e : Eligibility // e ∈ legalEligibility p}, ∀ c,
    ∑ p, positionLaw.w p * forcedSelectionProbability p (choice p).1 c ≤ 3 / lambda

end HypercubeRamsey
