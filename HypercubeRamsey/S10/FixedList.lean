import HypercubeRamsey.S10.Projection
import HypercubeRamsey.Framework.OneShot

/-!
# Section 10.1c: the fixed-list squared-mass test

This form allows each block to have its own first-side law and own/external status.
It therefore also covers the Part C use where every ID is treated as own but corner
laws may differ. The explicit hypotheses record the quantitative estimates used by the
test, in terms of the actual number `r` of blocks, instead of hiding them in informal
`O` notation.
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
external deletion ratio pass except with probability `exp(-c₅ a² k)`, for an absolute
`c₅ > 0`. The hypotheses are stated for arbitrary block laws, so a caller may mark every
block own while still using a different first-side law for each block.

The statement is generic in the discrepancy width `w` and error `ε`, the codegree gain
`a`, the block-law width `wμ` and the aggregate width `wν`. Section 10 uses
`w = n^η₀`, `ε = n^(-η₀)`, `a = n^(-δ)`, `wμ = wν = n^δ` (10:15–16, 10:85); Part C uses
the same `w, ε` with `a = θ/100` and `wμ = n^η₀ / 2`. The explicit hypotheses are the
quantitative facts the argument uses:
* `wν + log 4 + 2kr ≤ w`: the tilted prefix aggregate `D̄_J ≤ 4ν / A(J)` (10:75–79)
  keeps width at most `w` while all of the fewer than `kr` preceding ratios are at
  least `.24` (10:80–83);
* `(r+1) k r exp(wμ - w) ≤ exp(-a²k/50)`: a block law conditioned on an exceptional set
  of mass above `exp(wμ - w)` would fit the discrepancy width (10:85–87); `k r` counts
  the exposures and `r + 1` the orders (10:68, 10:99);
* `log (r+1) ≤ a²k/100`: the union over orders against the Azuma bound (10:99);
* `0 ≤ ε`, `100 ε ≤ a ≤ 1/10`: the discrepancy error is negligible against the gain
  (10:86–97). -/
def P10_1cFixedListTest : Prop :=
    ∃ c₅ : ℝ, 0 < c₅ ∧
      ∀ (N r k q : ℕ) (E : Fin N → Fin N → Prop)
        (X Y : Finset (Fin N)) (G : Colour)
        (ρ : FinProb (Fin q)) (D : Fin q → Law N) (ν : Law N)
        (μ : Fin r → Law N) (w ε a wμ wν : ℝ),
        (∀ b, (μ b).SupportedIn X ∧ (μ b).WidthLE wμ) →
        ν.WidthLE wν →
        (∀ j, (D j).SupportedIn Y) →
        (∀ y, (∑ j, ρ.w j * (D j).w y) ≤ 4 * ν.w y) →
        DiscOne E X Y w w ε →
        0 ≤ ε → 100 * ε ≤ a → a ≤ 1 / 10 →
        wν + Real.log 4 + 2 * (k : ℝ) * (r : ℝ) ≤ w →
        Real.log ((r : ℝ) + 1) ≤ a ^ 2 * (k : ℝ) / 100 →
        ((r : ℝ) + 1) * (k : ℝ) * (r : ℝ) * Real.exp (wμ - w) ≤
          Real.exp (-(a ^ 2 * (k : ℝ)) / 50) →
        fixedListFailureWeight (N := N) (r := r) (k := k) (q := q) E G ρ D μ a ≤
          Real.exp (-c₅ * a ^ 2 * (k : ℝ))

/-- P10.1c (10:56–99), as a reusable generic fixed-list result. -/
theorem p10_1c_fixed_list_squared_mass_test : P10_1cFixedListTest := by
  sorry

end HypercubeRamsey.S10
