import HypercubeRamsey.S08.L81.AnchorNodes

/-!
# Lemma 8.1, Step 11: odd loads by successive removal of constraints

Source: `sections/08-…tex`, lines 395–422 (L8.1k).
-/

noncomputable section

namespace HypercubeRamsey.S08

open Classical OAI.HypercubeRamsey
open scoped BigOperators

/-- The odd-moment constant `2(33K + 1)` (08:404–411). -/
def oddM (K : ℝ) : ℝ := 2 * (33 * K + 1)

namespace Ctx

variable {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)

/-- L8.1k, anchor stage (08:398–400): at a successful history, separated odd rows under the anchor law are bounded by
`2^l` times the raw-anchor mean of the products of `N p⁰/.98`. -/
def OddAnchorStep : Prop :=
  ∀ q : D.Pre, D.Good q → ∀ (y : Fin D.N) (l : ℕ), l ≤ D.n → ∀ u : Fin l → OddRole D.n,
    (∀ i j, i ≠ j → 8 < keyDist (keyOf η₀ (u i).1) (keyOf η₀ (u j).1)) →
    (D.anchorLaw q).expect (fun W => ∏ i, (D.N : ℝ) * D.prow q W (cellOf η₀ (u i).1) y) ≤
      2 ^ l * (D.rawAnchors q).expect (fun W => ∏ i, (D.N : ℝ) * D.p0 q W (cellOf η₀ (u i).1) y / (98 / 100))

/-- L8.1k, hidden stage (08:401–411): the pre-anchor mean of the raw-anchor products is at most `C^l`. -/
def OddHiddenStep (C : ℝ) : Prop :=
  ∀ (y : Fin D.N) (l : ℕ), l ≤ D.n → ∀ u : Fin l → OddRole D.n,
    (∀ i j, i ≠ j → 8 < keyDist (keyOf η₀ (u i).1) (keyOf η₀ (u j).1)) →
    D.preLaw.expect (fun q => (if D.Good q then 1 else 0) *
      (D.rawAnchors q).expect (fun W => ∏ i, (D.N : ℝ) * D.p0 q W (cellOf η₀ (u i).1) y / (98 / 100))) ≤ C ^ l

end Ctx

section Nodes

variable (η₀ γ β p K : ℝ) (h : ℕ)

/-- L8.1k(i) (08:398–400): `p ≤ p⁰/.98` pointwise (`PRowFacts`; `p = 0` off validity).  One anchor is touched by
`O(n^2)` grouped events, so removing the events touching the at most `2s l` cross anchors of the rows costs
`(1 - x_A)^{-O(s n^2 l)} ≤ 2^l` (`CondProductBound`); the integrand reads only those cross anchors (`P0Local`),
which then have their independent raw laws. -/
theorem odd_anchor_step (cA : ℝ) (hcA : 0 < cA) (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → CondProductBound →
      (∀ q : D.Pre, D.Good q → D.AnchorLLL q (2 * Real.exp (-(D.n : ℝ) ^ cA))) →
      D.P0Local → D.PRowFacts → D.OddAnchorStep := by
  sorry

/-- L8.1k(ii) (08:401–411): discard global selection success (validity stays inside `p⁰`); conditional on positions
and hidden tuples the rows read disjoint tags, activations, ties and cross anchors (grid scopes of radius three,
keys more than eight apart, `P0Local`), so the raw means factor; remove the at most `(2s+1)^2` hidden events
touching each target tuple (`(1 - x_H)^{-(2s+1)^2} ≤ 2` per row, `CondProductBound`); the targets then have their
independent priors and each factor is the raw mean of Step 7, at most `16K/(.98)` after normalization. -/
theorem odd_hidden_step (cH : ℝ) (hcH : 0 < cH) (hη₀ : 0 < η₀) (hK : 0 < K) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → CondProductBound →
      D.HiddenLLL (2 * Real.exp (-(D.n : ℝ) ^ cH)) → D.P0Local → D.P0RawMean K → D.P0Law →
      D.OddHiddenStep (33 * K + 1) := by
  sorry

/-- L8.1k, assembly of the two stages (08:396–413): the staged law draws the anchors from the anchor law at each
pre-anchor history, so the joint moment is the pre-anchor mean of the anchor-law means. -/
theorem odd_moment (D : Ctx η₀ β p h) (C : ℝ) (hC : 0 ≤ C) (hA : D.OddAnchorStep) (hH : D.OddHiddenStep C)
    (hP : D.PRowFacts) : D.OddMoment (2 * C) := by
  sorry

/-- L8.1k(iii) (08:415–422): Lemma 3.6 with labels for the odd rows on success: near rows have keys within distance
eight (fraction `f_grid`), the cap is `e^{.02 s log n}` and `n f_grid e^{.02 s log n} ≤ 1`; separated moments are
at most `C^l` (`OddMoment`); so the normalized average odd load exceeds `4(C+1)` with probability at most
`n 2^n 4^{-n}`, and otherwise the column sums are at most `2^{n-1} 4(C+1)/N ≤ 10⁻⁸`. -/
theorem odd_tail (C : ℝ) (hC : 0 ≤ C) (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → ∀ X Y R : Finset (Fin D.N), Std D γ K X Y R →
      GridFacts η₀ D.n → (10 : ℝ) ^ 8 * (4 * (C + 1)) * 2 ^ D.n ≤ D.N → D.PRowFacts → D.OddMoment C →
      D.stagedLaw.pr (fun z => D.Good z.1 ∧ ∃ y, (1e-8 : ℝ) < D.oddCol z.1 z.2 y) ≤
        (D.n : ℝ) * 2 ^ D.n * (1 / 4 : ℝ) ^ D.n := by
  sorry

end Nodes

end HypercubeRamsey.S08
