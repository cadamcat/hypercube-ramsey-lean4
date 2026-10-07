import HypercubeRamsey.Framework.FinProb

/-!
# Finite minimax and separation

The price-separation arguments of the paper (Lemma 3.3 and its uses in Sections 4–5 and later) in two forms.
-/

namespace HypercubeRamsey

/-- Finite minimax: if every mixed column strategy is answered by a row with nonpositive payoff, some mixed
row strategy has nonpositive payoff against every column. -/
theorem finite_minimax {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (M : A → B → ℝ) (h : ∀ q : FinProb B, ∃ a, ∑ b, q.w b * M a b ≤ 0) :
    ∃ p : FinProb A, ∀ b, ∑ a, p.w a * M a b ≤ 0 := sorry

/-- Separation in coordinates: a point outside the convex hull of finitely many vectors is strictly separated
by a linear functional. -/
theorem exists_separating_of_not_mem_convexHull {ι K : Type*} [Fintype ι] [Fintype K]
    (v : ι → K → ℝ) (p : K → ℝ)
    (h : ¬ ∃ ρ : FinProb ι, ∀ k, ∑ i, ρ.w i * v i k = p k) :
    ∃ c : K → ℝ, ∀ i, ∑ k, c k * v i k < ∑ k, c k * p k := sorry

end HypercubeRamsey
