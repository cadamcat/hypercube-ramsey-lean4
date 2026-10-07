import HypercubeRamsey.S12.Defs

/-!
# Heterogeneous centered moments
-/

namespace HypercubeRamsey.S12

open HypercubeRamsey
open Classical
open scoped BigOperators

/-- L12.2: the heterogeneous centered-moment expansion for arbitrary normalized finite weights. -/
theorem centered_moment_identity {N d u : ℕ}
    (τ : Fin N → ℝ) (hτ : ∑ x, τ x = 1)
    (π : Fin d → Fin N → ℝ) (hπ : ∀ l, ∑ y, π l y = 1)
    (φ : Fin d → Fin N → Fin N → ℝ) :
    ∑ ys : Fin d → Fin N,
        (∏ l, π l (ys l)) * ((∑ x, τ x * ∏ l, φ l x (ys l)) - 1) ^ u =
      ∑ xs : Fin u → Fin N,
        (∏ i, τ (xs i)) *
          ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
            ∏ l, ∑ y, π l y * ∏ i ∈ I, φ l (xs i) y := by
  sorry

/-- L12.2b: expand one column into all interaction subsets; positive degrees also kill singleton terms. -/
theorem column_expansion {N d u : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Fin d → Fin N → ℝ) (xs : Fin u → Fin N) (I : Finset (Fin u))
    (hπ : ∀ l, ∑ y, π l y = 1)
    (hdeg : ∀ l i, i ∈ I → 0 < deg E c (π l) (xs i)) :
    ∀ l,
      ((∑ y, π l y * ∏ i ∈ I, (1 + acoef E c (π l) (xs i) y)) =
        ∑ J ∈ I.powerset, inter E c (π l) J xs) ∧
      (∀ i ∈ I, inter E c (π l) ({i} : Finset (Fin u)) xs = 0) := by
  sorry

/-- L12.2: the two algebraic interfaces used by the moderate-moment estimate. -/
theorem centered_moment_export {N d u : ℕ}
    (τ : Fin N → ℝ) (hτ : ∑ x, τ x = 1)
    (π : Fin d → Fin N → ℝ) (hπ : ∀ l, ∑ y, π l y = 1)
    (φ : Fin d → Fin N → Fin N → ℝ)
    (E : Fin N → Fin N → Prop) (c : Colour)
    (xs : Fin u → Fin N) (I : Finset (Fin u))
    (hdeg : ∀ l i, i ∈ I → 0 < deg E c (π l) (xs i)) :
    (∑ ys : Fin d → Fin N,
        (∏ l, π l (ys l)) * ((∑ x, τ x * ∏ l, φ l x (ys l)) - 1) ^ u =
      ∑ xs : Fin u → Fin N,
        (∏ i, τ (xs i)) *
          ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
            ∏ l, ∑ y, π l y * ∏ i ∈ I, φ l (xs i) y) ∧
    (∀ l,
      ((∑ y, π l y * ∏ i ∈ I, (1 + acoef E c (π l) (xs i) y)) =
        ∑ J ∈ I.powerset, inter E c (π l) J xs) ∧
      (∀ i ∈ I, inter E c (π l) ({i} : Finset (Fin u)) xs = 0)) := by
  exact ⟨centered_moment_identity τ hτ π hπ φ,
    column_expansion E c π xs I hπ hdeg⟩

end HypercubeRamsey.S12
