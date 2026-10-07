import HypercubeRamsey.S10.Projection
import HypercubeRamsey.Framework.OneShot

/-!
# Section 10.1c: the fixed-list squared-mass test

This form allows each block to have its own first-side law and own/external status.
It therefore also covers the Part C use where every ID is treated as own but corner
laws may differ. The explicit growth hypotheses record the asymptotic estimates used
by the test instead of hiding them in informal `O` notation.
-/

namespace HypercubeRamsey.S10

open scoped BigOperators

/-- Product weight of a fixed array of independent first-side tuple entries. -/
def tupleArrayWeight {N r k : ℕ} (μ : Fin r → Law N)
    (W : Fin r → Fin k → Fin N) : ℝ :=
  ∏ b : Fin r, ∏ i : Fin k, (μ b).w (W b i)

/-- Labels joined to every entry of every block. -/
noncomputable def fixedListHitSet {N r k : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) (W : Fin r → Fin k → Fin N) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun y => ∀ b : Fin r, ∀ i : Fin k, Hits E G (W b i) y

/-- Common hits after deleting one block from the fixed list. -/
noncomputable def fixedListHitSetWithout {N r k : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) (W : Fin r → Fin k → Fin N) (deleted : Fin r) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun y =>
    ∀ b : Fin r, b ≠ deleted → ∀ i : Fin k, Hits E G (W b i) y

/-- Mass of a finite set under a finite law. -/
def lawMassOn {N : ℕ} (D : Law N) (A : Finset (Fin N)) : ℝ :=
  ∑ y ∈ A, D.w y

/-- Squared mass averaged over a finite mixture of cluster laws. -/
def squaredClusterMass {N q : ℕ} (ρ : FinProb (Fin q)) (D : Fin q → Law N)
    (A : Finset (Fin N)) : ℝ :=
  ∑ j : Fin q, ρ.w j * (lawMassOn (D j) A) ^ 2

/-- A block is own when every cluster with positive prior weight has high codegree
for every pair in that cluster's support. -/
def FixedListOwnBlock {N q : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (μ : Law N) (a : ℝ) : Prop :=
  ∀ j, 0 < ρ.w j → ∀ y y', 0 < (D j).w y → 0 < (D j).w y' →
    1 / 4 + a ≤ codeg E G μ y y'

/-- The failure event in the fixed-list test (10.1). -/
noncomputable def fixedListFailure {N r k q : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) (ρ : FinProb (Fin q)) (D : Fin q → Law N)
    (μ : Fin r → Law N) (a : ℝ) (W : Fin r → Fin k → Fin N) : Prop := by
  classical
  let F := fixedListHitSet E G W
  exact squaredClusterMass ρ D F < Real.exp (-2 * (k : ℝ) * (r : ℝ)) ∨
    (∃ b : Fin r,
      FixedListOwnBlock E G ρ D (μ b) a ∧
        squaredClusterMass ρ D F /
          squaredClusterMass ρ D (fixedListHitSetWithout E G W b) <
            Real.exp ((-Real.log 4 + (2 / 5 : ℝ) * a) * (k : ℝ))) ∨
    (∃ b : Fin r,
      ¬ FixedListOwnBlock E G ρ D (μ b) a ∧
        squaredClusterMass ρ D F /
          squaredClusterMass ρ D (fixedListHitSetWithout E G W b) <
            Real.exp (-2 * (k : ℝ)))

/-- Failure probability under the independent product sampling of all block entries. -/
noncomputable def fixedListFailureWeight {N r k q : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) (ρ : FinProb (Fin q)) (D : Fin q → Law N)
    (μ : Fin r → Law N) (a : ℝ) : ℝ := by
  classical
  exact ∑ W : (Fin r → Fin k → Fin N),
    if fixedListFailure E G ρ D μ a W then tupleArrayWeight μ W else 0

/-- P10.1c (10:56–99): for a fixed list, the absolute squared mass and every own or
external deletion ratio pass except with probability `exp(-c₅ a² k)`. The hypotheses
are stated for arbitrary block laws, so a caller may mark every block own while still
using a different first-side law for each block. -/
def P10_1cFixedListTest (η₀ δ : ℝ) (hη₀ : 0 < η₀) (hδ : 0 < δ)
    (hδsmall : δ < η₀ / 2000) : Prop :=
    ∃ c₅ : ℝ, 0 < c₅ ∧
      ∀ (n N r k m T q : ℕ) (E : Fin N → Fin N → Prop)
        (X Y : Finset (Fin N)) (G : Colour)
        (ρ : FinProb (Fin q)) (D : Fin q → Law N) (ν : Law N)
        (μ : Fin r → Law N),
        0 < n → 0 < N → 0 < k →
        (r : ℝ) ≤ (T + m + 1 : ℕ) →
        (∀ b, (μ b).SupportedIn X ∧ (μ b).WidthLE ((n : ℝ) ^ η₀)) →
        ν.SupportedIn Y → ν.WidthLE ((n : ℝ) ^ δ) →
        (∀ j, (D j).SupportedIn Y) →
        (∀ y, (∑ j, ρ.w j * (D j).w y) ≤ 4 * ν.w y) →
        DiscOne E X Y ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀) ((n : ℝ) ^ (-η₀)) →
        (n : ℝ) ^ (-δ) ≤ 1 / 10 →
        4 * Real.exp ((n : ℝ) ^ δ + 2 * (k : ℝ) * (T + m : ℕ)) ≤
          Real.exp ((n : ℝ) ^ η₀) →
        Real.log ((r : ℝ) + 1) ≤ ((n : ℝ) ^ (-2 * δ) * k) / 100 →
        ((r : ℝ) + 1) * Real.exp (-((n : ℝ) ^ η₀) / 2) ≤
          Real.exp (-((n : ℝ) ^ (-2 * δ) * k) / 100) →
        fixedListFailureWeight (N := N) (r := r) (k := k) (q := q)
          E G ρ D μ ((n : ℝ) ^ (-δ)) ≤
          Real.exp (-c₅ * (n : ℝ) ^ (-2 * δ) * k)

/-- P10.1c (10:56–99), as a reusable generic fixed-list result. -/
theorem p10_1c_fixed_list_squared_mass_test
    (η₀ δ : ℝ) (hη₀ : 0 < η₀) (hδ : 0 < δ)
    (hδsmall : δ < η₀ / 2000) : P10_1cFixedListTest η₀ δ hη₀ hδ hδsmall := by
  sorry

end HypercubeRamsey.S10
