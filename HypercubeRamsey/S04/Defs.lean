import HypercubeRamsey.Framework.Props

/-!
# Section 4 parameters and prepared pairs

Definitions from Part A §3.4 / Section 4, adapted to the repository's `PairProp` interface.
-/

namespace HypercubeRamsey

open scoped BigOperators

/-- D4.0 (04:29–36): the small exponent margin. -/
noncomputable def omega4 (β γ : ℝ) : ℝ := min β (1 - γ) / 1000

/-- D4.0 (04:29–36): the bias/purity exponent. -/
noncomputable def h4 (β γ : ℝ) : ℝ := omega4 β γ / 10 ^ 6

/-- D4.0 (04:55–80): a prepared patch with a plateau density in colour `G`.

The final clause is intrinsic to the supports of the prepared pair, as in the blueprint.
-/
def PrepLaw (β γ : ℝ) (G : Colour) : PairProp := fun n N E μ ν =>
  ∃ sX sY p : ℝ,
    (n : ℝ) ^ β ≤ sX ∧ sX ≤ 3 / 2 * (n : ℝ) ^ β ∧
    (n : ℝ) ^ γ ≤ sY ∧ sY ≤ 3 / 2 * (n : ℝ) ^ γ ∧
    μ.WidthLE sX ∧ ν.WidthLE (sY + 1) ∧
    1 / 2 + (n : ℝ) ^ (-h4 β γ) ≤ p ∧
    (∀ y, ν.w y ≠ 0 → p - (n : ℝ) ^ (-(omega4 β γ) / 5) ≤
      dens E G μ (Law.dirac y)) ∧
    (∀ μ' ν' : Law N,
      (∀ x, μ.w x = 0 → μ'.w x = 0) →
      (∀ y, ν.w y = 0 → ν'.w y = 0) →
      μ'.WidthLE (sX + (n : ℝ) ^ (β - omega4 β γ / 2) / 2) →
      ν'.WidthLE (sY + (n : ℝ) ^ (γ - omega4 β γ / 2) / 2) →
      dens E G μ' ν' ≤ p + (n : ℝ) ^ (-(omega4 β γ) / 3))

end HypercubeRamsey
