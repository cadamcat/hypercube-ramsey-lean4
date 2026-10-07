import HypercubeRamsey.Framework.FinProb

/-!
# Heavy-coordinate truncation

F-HeavyTrunc bounds the size and average-coordinate mass of labels with unusually large marginal, using a
pointwise cap on the joint law of a finite tuple.
-/

namespace HypercubeRamsey

open scoped BigOperators

/-- Average of the `k` coordinate marginals of a tuple law. -/
noncomputable def averageCoordinateMarginal {N k : ℕ} (P : FinProb (Fin k → Fin N))
    (x : Fin N) : ℝ :=
  (k : ℝ)⁻¹ * ∑ i, P.pr (fun ω => ω i = x)

/-- Coordinates whose normalized average marginal exceeds `exp(B)`. -/
noncomputable def heavyCoordinateSet {N k : ℕ} (P : FinProb (Fin k → Fin N)) (B : ℝ) :
    Finset (Fin N) :=
  Finset.univ.filter (fun x => Real.exp B < (N : ℝ) * averageCoordinateMarginal P x)

/-- F-HeavyTrunc: if `N^k P(ω) ≤ exp(A)` pointwise, then the heavy set is small and its average marginal
mass is controlled by `q/k + 2^k exp(A-Bq)` for every `q ≤ k`. -/
theorem heavyTruncation {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    (P : FinProb (Fin k → Fin N)) (A B : ℝ)
    (hcap : ∀ ω, (N : ℝ) ^ k * P.w ω ≤ Real.exp A) :
    let H := heavyCoordinateSet P B
    ((H.card : ℝ) ≤ (N : ℝ) * Real.exp (-B)) ∧
      (∀ q : ℕ, q ≤ k →
        ∑ x ∈ H, averageCoordinateMarginal P x ≤
          (q : ℝ) / k + (2 : ℝ) ^ k * Real.exp A * Real.exp (-B * q)) := by
  classical
  sorry

end HypercubeRamsey
