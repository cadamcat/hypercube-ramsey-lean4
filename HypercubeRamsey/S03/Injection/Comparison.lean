import HypercubeRamsey.S03.Injection.Sampler

/-!
# Lemma 3.9, the forcing comparison (TeX 03:695–734)

The likelihood identity extracts the target atom product before any failure
probability is used. Single-target forcing has its own concentration claim.
Zero atoms, repeated targets and the empty query are handled in the final
finite comparison node, not by taking a logarithm of a zero atom.
-/

namespace HypercubeRamsey.Injection

open Filter
open scoped BigOperators

def Targets {d t : ℕ} (S : Finset (Fin t)) (y : Fin t → Fin d) (x : Path t d) : Prop :=
  ∀ i ∈ S, x i = some (y i)

def PositiveDistinctTargets {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (S : Finset (Fin t)) (y : Fin t → Fin d) : Prop :=
  (∀ i ∈ S, 0 < q i (y i)) ∧ Set.InjOn y (↑S : Set (Fin t))

noncomputable def pendingMass {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (S : Finset (Fin t)) (y : Fin t → Fin d) (j : Fin t) : ℝ :=
  ∑ i ∈ S.filter (fun i => j.val < i.val), q j (y i)

noncomputable def excludedFraction {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (S : Finset (Fin t)) (y : Fin t → Fin d) (x : Path t d) (j : Fin t) : ℝ :=
  pendingMass q S y j / availableMass q x j ∅

/-- Residual after extracting the target atom product. -/
noncomputable def likelihoodFactor {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (S : Finset (Fin t)) (y : Fin t → Fin d) (x : Path t d) : ℝ :=
  (∏ i ∈ S, (availableMass q x i ∅)⁻¹) *
    ∏ j ∈ Finset.univ \ S, (1 - excludedFraction q S y x j)

noncomputable def linearError {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (S : Finset (Fin t)) (y : Fin t → Fin d) (x : Path t d) : ℝ :=
  -(∑ i ∈ S, Real.log (availableMass q x i ∅)) -
    ∑ j ∈ Finset.univ \ S, excludedFraction q S y x j

noncomputable def quadraticError {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (S : Finset (Fin t)) (y : Fin t → Fin d) (x : Path t d) : ℝ :=
  ∑ j ∈ Finset.univ \ S,
    |Real.log (1 - excludedFraction q S y x j) + excludedFraction q S y x j|

/-- TeX 03:699–705. Stated multiplicatively, so tiny target atoms are never divided out. -/
theorem forcing_likelihood_identity :
    ∀ᶠ d : ℕ in atTop, ∀ t (q : Fin t → Fin d → ℝ), OrderedInput d t q →
      ∀ (S : Finset (Fin t)) (y : Fin t → Fin d), PositiveDistinctTargets q S y → (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) →
      ∀ x, Good q x → Targets S y x →
        sequentialWeight q x = forcingWeight q S y x *
          (∏ i ∈ S, q i (y i)) * likelihoodFactor q S y x := by
  sorry

/-- TeX 03:709–713: weighted prefix versus the logarithmic uniform integral. -/
theorem prefix_log_comparison : ∃ K : ℝ, 1 ≤ K ∧
    ∀ d t (q : Fin t → Fin d → ℝ), OrderedInput d t q → ∀ (i : Fin t) y,
      |(∑ j : Fin t, if j.val < i.val then q j y / (1 - (j.val : ℝ) / d) else 0) +
        Real.log (1 - (i.val : ℝ) / d)| ≤ K * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
  sorry

/-- TeX 03:714–717: replacing tracked denominators and omitting queried steps. -/
theorem linear_likelihood_cancellation : ∃ K : ℝ, 1 ≤ K ∧
    ∀ d t (q : Fin t → Fin d → ℝ), OrderedInput d t q →
      ∀ (S : Finset (Fin t)) (y : Fin t → Fin d), PositiveDistinctTargets q S y → ∀ x, Good q x → Targets S y x →
      |linearError q S y x| ≤ K * S.card *
        ((d : ℝ) ^ (-(0.1 : ℝ)) + S.card * (d : ℝ) ^ (-(0.95 : ℝ))) := by
  sorry

/-- TeX 03:717–720: each excluded fraction is small, and the sum of squares is small. -/
theorem quadratic_likelihood_remainder : ∃ K : ℝ, 1 ≤ K ∧
    ∀ᶠ d : ℕ in atTop, ∀ t (q : Fin t → Fin d → ℝ), OrderedInput d t q →
      ∀ (S : Finset (Fin t)) (y : Fin t → Fin d), PositiveDistinctTargets q S y → (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) →
      ∀ x, Good q x → Targets S y x →
        (∀ j ∈ Finset.univ \ S, 0 ≤ excludedFraction q S y x j ∧
          excludedFraction q S y x j ≤ 1 / 2) ∧
        quadraticError q S y x ≤ K * (S.card : ℝ) ^ 2 * (d : ℝ) ^ (-(0.95 : ℝ)) := by
  sorry

/-- Algebra and exponent slack only: consumes the two log-error estimates. -/
theorem likelihood_log_transfer (K₁ K₂ : ℝ) (hK₁ : 1 ≤ K₁) (hK₂ : 1 ≤ K₂) :
    ∀ᶠ d : ℕ in atTop, ∀ t (q : Fin t → Fin d → ℝ), OrderedInput d t q →
      ∀ (S : Finset (Fin t)) (y : Fin t → Fin d), PositiveDistinctTargets q S y → (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) →
      ∀ x, Good q x → Targets S y x →
      |linearError q S y x| ≤ K₁ * S.card *
        ((d : ℝ) ^ (-(0.1 : ℝ)) + S.card * (d : ℝ) ^ (-(0.95 : ℝ))) →
      (∀ j ∈ Finset.univ \ S, 0 ≤ excludedFraction q S y x j ∧
        excludedFraction q S y x j ≤ 1 / 2) →
      quadraticError q S y x ≤ K₂ * (S.card : ℝ) ^ 2 * (d : ℝ) ^ (-(0.95 : ℝ)) →
        0 < likelihoodFactor q S y x ∧
        |Real.log (likelihoodFactor q S y x)| ≤ relativeError d / 4 * S.card := by
  sorry

/-- TeX 03:727–732: one reservation and one forced draw have only atom-scale cumulative drift cost. -/
theorem singleton_forcing_drift_stability :
    ∀ᶠ d : ℕ in atTop, ∀ t (q : Fin t → Fin d → ℝ), OrderedInput d t q →
      ∀ i y, 0 < q i (y i) → ∀ x a (b : Fin (t + 1)), RunningThrough q x b.val →
      |∑ j : Fin t, if j.val < b.val then
        forcedStepDrift q {i} y x a j - stepDrift q x a j else 0| ≤
        1000 * (d : ℝ) ^ (-(0.95 : ℝ)) := by
  sorry

/-- Concentration is under the forcing law, independent of the target's atom size. -/
theorem forced_martingale_concentration :
    ∀ᶠ d : ℕ in atTop, ∀ t (q : Fin t → Fin d → ℝ) (h : OrderedInput d t q),
      ∀ i y, 0 < q i (y i) → 1 - failureBound d ≤
        (forcingLaw q h.nonneg h.row_sum {i} y).pr (ForcedMartingaleGood q {i} y) := by
  sorry

/-- Reuses the deterministic recurrence with the forced martingale and drift change. -/
theorem singleton_forcing_tracking_transfer (K : ℝ) (hK : 1 ≤ K) :
    ∀ᶠ d : ℕ in atTop, ∀ t (q : Fin t → Fin d → ℝ) (h : OrderedInput d t q),
      DriftRecurrence q K → ∀ i y, 0 < q i (y i) →
      (∀ x a (b : Fin (t + 1)), RunningThrough q x b.val →
        |∑ j : Fin t, if j.val < b.val then
          forcedStepDrift q {i} y x a j - stepDrift q x a j else 0| ≤
            1000 * (d : ℝ) ^ (-(0.95 : ℝ))) →
      1 - failureBound d ≤
        (forcingLaw q h.nonneg h.row_sum {i} y).pr (ForcedMartingaleGood q {i} y) →
      1 - failureBound d ≤ (forcingLaw q h.nonneg h.row_sum {i} y).pr (Good q) := by
  sorry

/-- TeX 03:722–734: integrate the atom-extracted ratio and condition on G.
The conclusion quantifies over all queries, including empty, zero and repeated targets. -/
theorem conditioned_comparison_transfer :
    ∀ᶠ d : ℕ in atTop, ∀ t (q : Fin t → Fin d → ℝ) (h : OrderedInput d t q),
      1 - failureBound d ≤ (sequentialLaw q h.nonneg h.row_sum).pr (Good q) →
      (∀ (S : Finset (Fin t)) (y : Fin t → Fin d), PositiveDistinctTargets q S y → (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) →
        ∀ x, Good q x → Targets S y x → sequentialWeight q x = forcingWeight q S y x *
          (∏ i ∈ S, q i (y i)) * likelihoodFactor q S y x) →
      (∀ (S : Finset (Fin t)) (y : Fin t → Fin d), PositiveDistinctTargets q S y → (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) →
        ∀ x, Good q x → Targets S y x → 0 < likelihoodFactor q S y x ∧
          |Real.log (likelihoodFactor q S y x)| ≤ relativeError d / 4 * S.card) →
      (∀ i y, 0 < q i (y i) →
        1 - failureBound d ≤ (forcingLaw q h.nonneg h.row_sum {i} y).pr (Good q)) →
      ∃ hG : 0 < (sequentialLaw q h.nonneg h.row_sum).pr (Good q),
        (∀ x, (conditionedLaw q h hG).w x ≠ 0 → Function.Injective x) ∧
        (∀ (S : Finset (Fin t)) (y : Fin t → Fin d), (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) →
          (conditionedLaw q h hG).pr (fun x => ∀ i ∈ S, x i = y i) ≤
            Real.exp (relativeError d * S.card) * ∏ i ∈ S, q i (y i)) ∧
        (∀ i y, |(conditionedLaw q h hG).pr (fun x => x i = y) - q i y| ≤
          relativeError d * q i y) := by
  sorry

end HypercubeRamsey.Injection
