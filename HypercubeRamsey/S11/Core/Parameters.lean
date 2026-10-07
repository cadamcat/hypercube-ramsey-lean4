import HypercubeRamsey.S11.Core.Definitions

namespace HypercubeRamsey.S11.Core

/-- Elementary exponent separations used uniformly by the finite Section 11 experiments. -/
noncomputable def ScaleBounds (n : ℕ) (δ x₀ h₀ κ : ℝ) : Prop :=
  5 ≤ innerDimension n ∧
  2 ≤ tupleLength n ∧
  100 * (n : ℝ) ^ (1 / 100 : ℝ) ≤
    sliceSurplus n * (innerDimension n : ℝ) ∧
  4 * signedBiasScale n ≤ (n : ℝ) ^ (-δ) / 4 ∧
  (n : ℝ) ^ ((13 : ℝ) / 20) ≤ (n : ℝ) ^ (1 - δ / 16) / 2 ∧
  (n : ℝ) ^ (3 / 100 : ℝ) + (n : ℝ) ^ (1 / 20 : ℝ) + 100 ≤
    sliceSurplus n * (innerDimension n : ℝ) / 4 ∧
  10 ≤ (n : ℝ) ^ (x₀ / 2) ∧
  10 ≤ (n : ℝ) ^ (h₀ / 2) ∧
  0 < κ

/-- P11.1-parameters: for fixed positive exponents, all Section 11 scale inequalities hold eventually. -/
theorem exists_scale_bounds (δ x₀ h₀ κ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 20000)
    (hx : 0 < x₀) (hx' : x₀ < 1) (hh : 0 < h₀) (hh' : h₀ < 1 / 100) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ScaleBounds n δ x₀ h₀ κ := by
  sorry

end HypercubeRamsey.S11.Core
