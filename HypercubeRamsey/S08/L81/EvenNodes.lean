import HypercubeRamsey.S08.L81.OddNodes
import HypercubeRamsey.S03.ClockSampling

/-!
# Lemma 8.1, Step 12: injection, even loads and Hall

Source: `sections/08-…tex`, lines 424–454 (L8.1l).
-/

noncomputable section

namespace HypercubeRamsey.S08

open Classical OAI.HypercubeRamsey
open scoped BigOperators

section Nodes

variable (η₀ γ β p K : ℝ) (h : ℕ)

/-- L8.1l(i) (08:425–426): on a successful prehistory every odd task is valid (the denominator and hit tests pass
and the rest of validity holds on success), so the odd rows are probability laws with atoms at most
`e^{.02 s log n}/N ≤ n^{-A}` and column sums at most `10⁻⁸`; Lemma 3.10 (`clock_sampling`, `B = 3`, `C_g = 2`)
with the predictive failures at the even vertices as forbidden predicates (scope the `n` odd neighbours, each odd
row in at most `n` scopes, product-law probability the alarm rate `≤ e^{-.02n} ≤ n^{-P}`) gives an injective odd
assignment avoiding every predictive failure with joint comparison `1 + εn ≤ 2` on at most `n^3` rows. -/
theorem clock_rows (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → (2 : ℝ) ^ D.n ≤ D.N →
      D.N ≤ D.n * 2 ^ D.n → D.SelConseq → D.PRowFacts →
      ∀ (q : D.Pre) (W : D.Anch), D.Good q → D.GoodPre q W → ∃ J, D.ClockOK q W J := by
  sorry

/-- L8.1l(ii) (08:427–432): on predictive success `M_v > 0`, so the posterior row is a probability law; a label in its
support has `F_x(y) ≠ 0`, so every neighbouring odd row, recomputed with `v`'s anchor equal to `x`, is positive at
its label; `v`'s cell is a padded even neighbour of each neighbour's cell (edge cover), so the label hits `x`. -/
theorem evenRow_law (D : Ctx η₀ β p h) (hG : GridFacts η₀ D.n) (hP : D.PRowFacts) : D.EvenRowLaw := by
  sorry

/-- L8.1l(iii) (08:433–437): on success the selected tag passes its cutoffs, so
`N max U_v ≤ e^{n^γ + log 2 + n^{2τ}}/(1-Δ) = e^{o(n)}`; with `F_x ≤ e^{.03n} Q_v` and `M_v ≥ e^{-.04n} Q_v`,
`N max w_v ≤ e^{.1n}` for large `n`. -/
theorem evenRow_cap (hη₀ : 0 < η₀) (hγ₁ : γ < 1) (hp : 0 < p) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → ∀ X Y R : Finset (Fin D.N), Std D γ K X Y R →
      GridFacts η₀ D.n → D.StarLikBound → D.SelConseq → D.EvenRowCap := by
  sorry

/-- L8.1l(iv) (08:441–449): integrating the role's anchor and the product neighbour data gives the data subdensity
`M_v`, which cancels the posterior denominator: `Σ_y M_v(y) w_v(x; y) 1[success] ≤ U_v(x) Σ_y F_x(y) ≤ U_v(x)`. -/
theorem star_cancel (D : Ctx η₀ β p h) (hU : D.StarRefUpdate) (hP : D.PRowFacts) : D.StarCancel := by
  sorry

/-- L8.1l(v) (08:439): residual-separated even roles have disjoint odd neighbourhoods; the clock law is supported
on predictive success and its joint comparison on the at most `n^2` neighbouring odd labels replaces the injection
by independent draws from the odd rows; the integral factors into the star integrals. -/
theorem clock_factor (D : Ctx η₀ β p h) (q : D.Pre) (J : D.Anch → FinProb (OddRole D.n → Fin D.N))
    (hJ : ∀ W, D.GoodPre q W → D.ClockOK q W (J W)) (hP : D.PRowFacts) : D.ClockFactor q J := by
  sorry

/-- L8.1l(vi) (08:439–449): remove the anchor events touching the separated target anchors (at most
`(2s + n - m + 1)^2` each, factor `2` per role, `CondProductBound`); each star integral reads anchors within cell
distance two of its own target only (targets more than four apart), so the targets integrate independently and
`StarCancel` bounds each factor. -/
theorem even_anchor_integral (cA : ℝ) (hcA : 0 < cA) (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → CondProductBound → D.StarCancel →
      D.PRowFacts → ∀ q : D.Pre, D.Good q → D.AnchorLLL q (2 * Real.exp (-(D.n : ℝ) ^ cA)) →
        D.EvenAnchorIntegral q := by
  sorry

/-- L8.1l(vii) (08:439–453): the clock comparison at every successful prehistory and the anchor integral give
`4^l ∏ N U(x)` (for `l = 0` both sides are at most one). -/
theorem even_moment (D : Ctx η₀ β p h) (q : D.Pre) (J : D.Anch → FinProb (OddRole D.n → Fin D.N))
    (hP : D.PRowFacts) (hfac : D.ClockFactor q J) (hint : D.EvenAnchorIntegral q) : D.EvenMoment q J := by
  sorry

/-- L8.1l(viii) (08:450–454): Lemma 3.6 with labels for the even rows at a fixed successful history with the
selected-anchor load bound: near roles have residual words within distance four (fraction at most
`2(n+1)^4 2^{-(n-m)}`), the cap is `e^{.1n}` on predictive success, `n f e^{.1n} ≤ 1`, the comparison means are
the selected laws (average at most `C_L`), separated moments are at most `4^l ∏ N U(x)`; so the normalized even load
exceeds `16(C_L + 1)` with probability at most `n 2^n 4^{-n}`, and otherwise the column sums are at most
`2^{n-1} 16(C_L + 1)/N ≤ 1`. -/
theorem even_tail (CL : ℝ) (hCL : 0 ≤ CL) (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → D.N ≤ D.n * 2 ^ D.n →
      16 * (CL + 1) * 2 ^ D.n ≤ D.N → D.EvenRowCap → D.PRowFacts → D.SelConseq →
      ∀ q : D.Pre, D.Good q → D.LoadOK CL q →
        ∀ J : D.Anch → FinProb (OddRole D.n → Fin D.N), (∀ W, D.GoodPre q W → D.ClockOK q W (J W)) →
          D.EvenMoment q J →
          ∑ W, (D.anchorLaw q).w W *
              (if D.GoodPre q W then (J W).pr (fun f => ∃ x, 1 < D.evenCol q W f x) else 0) ≤
            (D.n : ℝ) * 2 ^ D.n * (1 / 4 : ℝ) ^ D.n := by
  sorry

end Nodes

end HypercubeRamsey.S08
