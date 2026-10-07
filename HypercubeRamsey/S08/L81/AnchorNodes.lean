import HypercubeRamsey.S08.L81.LoadNodes

/-!
# Lemma 8.1, Step 10: anchor avoidance and predictive alarms

Source: `sections/08-…tex`, lines 365–393 (L8.1j).
-/

noncomputable section

namespace HypercubeRamsey.S08

open Classical OAI.HypercubeRamsey
open scoped BigOperators

section Nodes

variable (η₀ γ β p K : ℝ) (h : ℕ)

/-- L8.1j(i) (08:366): on a successful history the presentation of `c` other than its cross anchors is fixed and
legitimate, the gates hold, and the cross anchors are independent with laws `U_{u,i}` of the selected cross tags;
so the raw probability of `M < ε₀` is `q_L` of the used list, at most `ε₀^{1/4}` (`SelConseq`). -/
theorem den_fail_prob (D : Ctx η₀ β p h) (hS : D.SelConseq) : D.DenFailProb := by
  sorry

/-- L8.1j(ii) (08:366, 295–297): when the denominator test passes on a successful history the presentation is
valid; integrating the ordinary anchors (independent of the cross anchors and of validity) by `HitTail` bounds the
hit-test failure. -/
theorem hit_fail_prob (D : Ctx η₀ β p h) (hS : D.SelConseq) (hT : D.HitTail) : D.HitFailProb := by
  sorry

/-- L8.1j(iii) (08:377–381): at a neighbour of the same key `p ≤ p⁰/.98` with `p⁰` the reference factor (`p⁰` there
does not read `v`'s anchor, an ordinary anchor of that cell); at the at most `m` other neighbours
`p ≤ e^{.02 s log n}/N`; so `F_z ≤ .98^{-n} e^{.02 s log n · m} Q_v ≤ e^{.03n} Q_v` (`ms log n = o(n)`). -/
theorem starLik_bound (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → D.PRowFacts → D.StarLikBound := by
  sorry

/-- L8.1j(iv) (08:377–378): each factor of `Q_v` is `p⁰` (with its validity) at a neighbour cell of the same key,
which reads only that cell's cross anchors, not the anchor of `v`'s cell; the other factors are constant. -/
theorem starRef_update (D : Ctx η₀ β p h) : D.StarRefUpdate := by
  sorry

/-- L8.1j(v) (08:383–385): predictive failure does not depend on `z` (`M_v` integrates it, `Q_v` does not read it);
the joint probability of failure under the raw target anchor and product neighbour sampling is
`Σ_y M_v(y) 1[fail] ≤ e^{-.04n} Σ_y Q_v(y) ≤ e^{-.04n}` (Lemma 3.7, first assertion). -/
theorem alarm_mean (D : Ctx η₀ β p h) (hU : D.StarRefUpdate) : D.AlarmMean := by
  sorry

/-- L8.1j(vi) (08:385–389): Markov bounds by `e^{-.02n}` the anchor probability of one vertex's alarm; the alarm
rate of an even vertex depends on the vertex only through its neighbour-cell multiplicity profile (the number of
special-bit neighbours in each cross bin or the own bin, at most `(n+1)^{2s+1}` profiles per cell), so the
grouped alarm of a cell has probability at most `(n+1)^{2s+1} e^{-.02n}`. -/
theorem alarm_prob (D : Ctx η₀ β p h) (hG : GridFacts η₀ D.n) (hA : D.AlarmMean) : D.AlarmProb := by
  sorry

/-- L8.1j(vii) (08:387): the denominator and hit tests of `c` read anchors within cell distance one, an alarm at `c`
reads the rows of the neighbour cells of its vertices (cell distance one, by the edge cover), which read anchors
within distance one of those. -/
theorem cellBad_scope (D : Ctx η₀ β p h) (hG : GridFacts η₀ D.n) : D.CellBadScope := by
  sorry

/-- L8.1j(viii) (08:387–393): on a successful history the grouped cell events have raw probability at most
`q_A ≤ ε₀^{1/4} + 50(n+1)Δ/(1-Δ) + (n+1)^{2s+1}e^{-.02n} ≤ e^{-n^{c_A}}`, scopes the radius-two cell balls, and
dependency degree at most `(2s + (n-m) + 1)^4`; `x_A = 2q_A` meets the local-lemma condition. -/
theorem anchor_lll (hη₀ : 0 < η₀) (hp : 0 < p) (hh : 1 ≤ h) :
    ∃ cA > (0 : ℝ), ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n →
      D.DenFailProb → D.HitFailProb → D.AlarmProb → D.CellBadScope →
      ∀ q : D.Pre, D.Good q → D.AnchorLLL q (2 * Real.exp (-(D.n : ℝ) ^ cA)) := by
  sorry

end Nodes

end HypercubeRamsey.S08
