import Mathlib

/-!
# Finite-dimensional Kuhn mesh

F-Mesh returns a locally supported continuous partition of unity on a compact convex parameter set. The
active-vertex bound `D+1` is essential to the finite history-count estimates in Part C.
-/

namespace HypercubeRamsey

open scoped BigOperators

/-- F-Mesh (X-Kuhn): for any nonempty compact convex `K ⊆ ℝ^D` and `r > 0`, there is a finite family of
continuous partition-of-unity weights whose positive support has at most `D+1` vertices, each based in `K`
within coordinate distance `r` of the parameter. -/
theorem exists_finite_mesh (D : ℕ) (K : Set (Fin D → ℝ)) (hKne : K.Nonempty)
    (hKcompact : IsCompact K) (hKconvex : Convex ℝ K) (r : ℝ) (hr : 0 < r) :
    ∃ m : ℕ,
      ∃ base : Fin m → {p : Fin D → ℝ // p ∈ K},
      ∃ weight : Fin m → {p : Fin D → ℝ // p ∈ K} → ℝ,
        (∀ v, Continuous (weight v)) ∧
        (∀ v p, 0 ≤ weight v p) ∧
        (∀ p, ∑ v, weight v p = 1) ∧
        (∀ v p, 0 < weight v p → ∀ j : Fin D,
          |p.1 j - (base v).1 j| ≤ r) ∧
        (∀ p, (Finset.univ.filter (fun v => 0 < weight v p)).card ≤ D + 1) := by
  sorry

end HypercubeRamsey
