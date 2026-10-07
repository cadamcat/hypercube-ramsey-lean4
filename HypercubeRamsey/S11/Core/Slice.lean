import HypercubeRamsey.S11.Core.Definitions
import HypercubeRamsey.S03.GatedPosterior

/-!
# Proposition 11.1: the biased menu and the slice experiment

Source: `sections/11-…tex`, lines 26–89 (P11.1-menu, P11.1a, P11.1b in `research/blueprint/PART-B.md` §3.11).
-/

namespace HypercubeRamsey.S11.Core

open HypercubeRamsey OAI.HypercubeRamsey
open Classical
open scoped BigOperators

/-- P11.1-menu (11:26–33).  Availability of `PBias(n^.01, .01n, h₀)` at tolerance `κ` gives availability of one
colour sign at tolerance `κ/2` (F-UnionAvail: two bad removal pairs of size `κN/2` would combine into one of size
`κN`).  For a witness `(μ, ν)` of colour `G`, `E_ν d_G(μ, y) ≥ 1/2 + n^{-h₀}` and `d_G ≤ 1`, so the columns of
degree at least `1/2 + 2g` carry `ν`-mass at least `2(n^{-h₀} - 2g) ≥ n^{-h₀}` (as `h₀ < .01`); conditioning `ν`
on them costs at most `h₀ log n ≤ .001 n` width.  Index the menu by the removal pairs of size at most `κN/2` and
choose one restricted witness for each. -/
theorem biased_menu (h₀ κ : ℝ) (hh₀ : 0 < h₀) (hh₀' : h₀ < 1 / 100) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)},
      AvailableAt κ (PBias (pw ((1 / 100 : ℚ) : ℝ)) (lw ((1 / 100 : ℚ) : ℝ)) h₀).toPatch n N E X Y →
      Nonempty (Menu11 n N E X Y (κ / 2)) := by
  sorry

/-- P11.1a(i) (11:52–56, 11:65).  Provisionally draw `Y₀ ∼ ν`, then the `kh` entries `W ∼ ρ_{Y₀}^{⊗kh}`.  Relative
to the reference `μ^{⊗kh}` the marginal density of `W` is `Z_b(W)`, so Lemma 3.7 (`gated_posterior`, first
assertion, `ε = e^{-kh}`) bounds the probability of `Z_b < e^{-kh}` or `Z_b = 0` by `e^{-kh}`.  For the deletion
test of direction `a`, use the posterior of `Y₀` given the other tuples as prior and the reference `μ^{⊗k}` for
the tuple of `a`: its predictive density is `Z_b / Z_{b,-a}`, and Lemma 3.7 with `ε = e^{-.2gk}` bounds the
failure.  The `ν`-average of `testFail` is therefore at most `e^{-kh} + h e^{-.2gk}`, and some `y₀ ∈ supp ν`
attains at most the average.  Every label of `supp ν` has positive degree, so `ρ_{y₀}` is the hit-conditioned
law. -/
theorem base_label {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (I : Type) [Fintype I] [DecidableEq I]
    (k : ℕ) (g : ℝ) (μ ν : Law N) (hdeg : ∀ y, ν.w y ≠ 0 → 0 < colDeg E G μ y) :
    ∃ y₀, ν.w y₀ ≠ 0 ∧ testFail E G I k g μ ν y₀ ≤
      Real.exp (-((k : ℝ) * Fintype.card I)) + (Fintype.card I : ℝ) * Real.exp (-(1 / 5 : ℝ) * g * k) := by
  sorry

/-- The row facts of P11.1a(ii) and of the mean odd row `π_i` (11:57–63, 11:100). -/
structure RowFacts {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (I : Type) [Fintype I] [DecidableEq I]
    (k : ℕ) (g : ℝ) (μ ν : Law N) (y₀ : Fin N) (L : ℝ) : Prop where
  row_nonneg : ∀ (ws : I → Fin k → Fin N) y, 0 ≤ oddRowW E G g μ ν ws y
  row_sum : ∀ ws : I → Fin k → Fin N, ∑ y, oddRowW E G g μ ν ws y = 1
  row_supp : ∀ (ws : I → Fin k → Fin N) y, oddRowW E G g μ ν ws y ≠ 0 → ν.w y ≠ 0
  row_cap : ∀ (ws : I → Fin k → Fin N) y, (N : ℝ) * oddRowW E G g μ ν ws y ≤ L
  pi_nonneg : ∀ y, 0 ≤ meanOddRow E G I k g μ ν y₀ y
  pi_sum : ∑ y, meanOddRow E G I k g μ ν y₀ y = 1
  pi_supp : ∀ y, meanOddRow E G I k g μ ν y₀ y ≠ 0 → ν.w y ≠ 0
  pi_cap : ∀ y, (N : ℝ) * meanOddRow E G I k g μ ν y₀ y ≤ L

/-- P11.1a(ii) (11:57–63, 11:100).  A passing row is `ν L_b / Z_b` with `Z_b ≥ e^{-kh} > 0`, `N ν ≤ e^{.011n}` and
`L_b ≤ (1/2 + 2g)^{-kh}` on `supp ν`, so `log(N max p_b^W) ≤ .011n + kh(1 - log(1/2 + 2g)) ≤ .02n` as
`kh = O(n^{.3})`; the fallback row is `ν`.  The tuple weights at `y₀ ∈ supp ν` sum to one (`d_G(μ, y₀) > 0`), so
`π_i` is an average of rows. -/
theorem odd_row_facts :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (μ ν : Law N) (y₀ : Fin N),
      ν.WidthLE ((11 / 1000 : ℝ) * n) → (∀ y, ν.w y ≠ 0 → 1 / 2 + 2 * gS n ≤ colDeg E G μ y) →
      ν.w y₀ ≠ 0 →
      RowFacts E G (InnerCoord n) (kTup n) (gS n) μ ν y₀ (Real.exp ((n : ℝ) / 50)) := by
  sorry

/-- P11.1b (11:66–90).  Fix the radius-two data except the centre tuple `w` (prior `ρ_{y₀}^{⊗k}`).  For internal
outputs `t`, `F_w(t)` is the product of the `h` neighbouring rows times the indicator that their tests pass;
each passing row is at most `(1/2 + 2g)^{-k} e^{.2gk}` times its deletion row, so `F_w(t) ≤ e^{(log 2-2g)kh} Q(t)`
with `Q` the product of the deletion rows (fixed fallbacks at zero denominators).  Lemma 3.7 bounds the event
`m = 0` or `m < e^{-.5gkh} Q` by `e^{-.5gkh}`.  Outside it the posterior of `w` has atoms at most
`N^{-k} e^{(log 2 - 1.5g)kh + k n^{.01} + O(k)} ≤ N^{-k} e^{(log 2 - g)kh}` (`width μ ≤ n^.01 = o(gh)`) and is
supported on tuples of common neighbours, so the common-neighbour set has at least `N e^{-(log 2 - g)h}` labels,
above the cutoff.  Each of the `h` neighbouring rows fails its tests with probability `testFail` (its `h` tuples
are independent `ρ_{y₀}^{⊗k}` draws). -/
theorem sigma_fail :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (μ ν : Law N) (y₀ : Fin N),
      μ.WidthLE ((n : ℝ) ^ ((1 : ℝ) / 100)) → (∀ y, ν.w y ≠ 0 → 1 / 2 + 2 * gS n ≤ colDeg E G μ y) →
      ν.w y₀ ≠ 0 →
      sigmaFail E G (InnerCoord n) (kTup n) (gS n) μ ν y₀ ≤
        Real.exp (-(1 / 2 : ℝ) * gS n * kTup n * Fintype.card (InnerCoord n)) +
          (Fintype.card (InnerCoord n) : ℝ) * testFail E G (InnerCoord n) (kTup n) (gS n) μ ν y₀ := by
  sorry

/-- The facts of the mean even row `α_i` (11:100). -/
structure AlphaFacts {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (I : Type) [Fintype I] [DecidableEq I]
    (k : ℕ) (g : ℝ) (μ ν : Law N) (y₀ : Fin N) : Prop where
  nonneg : ∀ x, 0 ≤ meanEvenRow E G I k g μ ν y₀ x
  sum_le : ∑ x, meanEvenRow E G I k g μ ν y₀ x ≤ 1
  supp : ∀ x, meanEvenRow E G I k g μ ν y₀ x ≠ 0 → μ.w x ≠ 0

/-- `α_i` is a subprobability on `supp μ_i` (11:100): `σ_v` has mass zero or one on the common-neighbour set
inside `supp μ_i`, and the tuple and output weights are probabilities. -/
theorem alpha_facts {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (I : Type) [Fintype I] [DecidableEq I]
    (k : ℕ) (g : ℝ) (μ ν : Law N) (y₀ : Fin N)
    (hrow0 : ∀ (ws : I → Fin k → Fin N) y, 0 ≤ oddRowW E G g μ ν ws y)
    (hrow1 : ∀ ws : I → Fin k → Fin N, ∑ y, oddRowW E G g μ ν ws y = 1) :
    AlphaFacts E G I k g μ ν y₀ := by
  sorry

/-- All slice facts of a menu with base labels (P11.1a, P11.1b). -/
structure SliceFacts {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
    (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) : Prop where
  base : ∀ i, (M.ν i).w (y₀ i) ≠ 0
  test : ∀ i, testFail E M.G (InnerCoord n) (kTup n) (gS n) (M.μ i) (M.ν i) (y₀ i) ≤
    Real.exp (-((kTup n : ℝ) * Fintype.card (InnerCoord n))) +
      (Fintype.card (InnerCoord n) : ℝ) * Real.exp (-(1 / 5 : ℝ) * gS n * kTup n)
  rows : ∀ i, RowFacts E M.G (InnerCoord n) (kTup n) (gS n) (M.μ i) (M.ν i) (y₀ i) (Real.exp ((n : ℝ) / 50))
  sigma : ∀ i, sigmaFail E M.G (InnerCoord n) (kTup n) (gS n) (M.μ i) (M.ν i) (y₀ i) ≤
    Real.exp (-(1 / 2 : ℝ) * gS n * kTup n * Fintype.card (InnerCoord n)) +
      (Fintype.card (InnerCoord n) : ℝ) * testFail E M.G (InnerCoord n) (kTup n) (gS n) (M.μ i) (M.ν i) (y₀ i)
  alpha : ∀ i, AlphaFacts E M.G (InnerCoord n) (kTup n) (gS n) (M.μ i) (M.ν i) (y₀ i)

/-- P11.1a–b assembled: base labels with all slice facts. -/
theorem slice_facts :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
      (M : Menu11 n N E X Y κ), ∃ y₀ : M.ι → Fin N, SliceFacts M y₀ := by
  obtain ⟨n₁, hrow⟩ := odd_row_facts
  obtain ⟨n₂, hsig⟩ := sigma_fail
  refine ⟨max n₁ n₂, ?_⟩
  intro n hn N E X Y κ M
  have hn₁ : n₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : n₂ ≤ n := le_trans (le_max_right _ _) hn
  have hg : (0 : ℝ) < 1 / 2 + 2 * gS n := by unfold gS; positivity
  have hdeg : ∀ i y, (M.ν i).w y ≠ 0 → 0 < colDeg E M.G (M.μ i) y :=
    fun i y hy => lt_of_lt_of_le hg (M.high i y hy)
  choose y₀ hy₀ using fun i =>
    base_label E M.G (InnerCoord n) (kTup n) (gS n) (M.μ i) (M.ν i) (hdeg i)
  have hR : ∀ i, RowFacts E M.G (InnerCoord n) (kTup n) (gS n) (M.μ i) (M.ν i) (y₀ i)
      (Real.exp ((n : ℝ) / 50)) :=
    fun i => hrow n hn₁ E M.G (M.μ i) (M.ν i) (y₀ i) (M.ν_width i) (M.high i) (hy₀ i).1
  exact ⟨y₀, {
    base := fun i => (hy₀ i).1
    test := fun i => (hy₀ i).2
    rows := hR
    sigma := fun i => hsig n hn₂ E M.G (M.μ i) (M.ν i) (y₀ i) (M.μ_width i) (M.high i) (hy₀ i).1
    alpha := fun i => alpha_facts E M.G (InnerCoord n) (kTup n) (gS n) (M.μ i) (M.ν i) (y₀ i)
      (hR i).row_nonneg (hR i).row_sum }⟩

end HypercubeRamsey.S11.Core
