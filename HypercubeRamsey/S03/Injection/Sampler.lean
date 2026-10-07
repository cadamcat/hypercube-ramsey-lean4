import HypercubeRamsey.Framework.FinProb

/-!
# Lemma 3.9, the stopped sequential process (TeX 03:649–693)

Indices are zero based: time `b` means that rows `0,…,b-1` have been drawn.
The terminal time `t` is included. `none` is an absorbing failure, so the law
is defined even when a free-label denominator vanishes. All weights below
are concrete; the normalization and analytic estimates are proof nodes.
-/

namespace HypercubeRamsey.Injection

open Filter Classical
open scoped BigOperators

abbrev Path (t d : ℕ) := Fin t → Option (Fin d)

/-- The slack away from full occupancy is needed for all denominator estimates. -/
structure OrderedInput (d t : ℕ) (q : Fin t → Fin d → ℝ) : Prop where
  dimension : 100 ≤ d
  horizon : (t : ℝ) ≤ 3 * (d : ℝ) / 4
  nonneg : ∀ i y, 0 ≤ q i y
  row_sum : ∀ i, ∑ y, q i y = 1
  atom : ∀ i y, q i y ≤ 10 * (d : ℝ) ^ (-(0.95 : ℝ))
  column_prefix : ∀ (b : Fin (t + 1)) y,
    |(∑ k : Fin t, if k.val < b.val then q k y else 0) -
      (b.val : ℝ) / d| ≤ 10 * (d : ℝ) ^ (-(1 / 8 : ℝ))

noncomputable def usedMass {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (x : Path t d) (a : Fin t) (b : ℕ) : ℝ :=
  ∑ k : Fin t, if k.val < b then (x k).elim 0 (q a) else 0

/-- Finite maximum, including zero so it is defined for no rows. -/
noncomputable def trackingError {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (x : Path t d) (b : ℕ) : ℝ :=
  sSup ({0} ∪ {r | ∃ a : Fin t, ∃ k : Fin (t + 1),
    k.val ≤ b ∧ r = |usedMass q x a k.val - (k.val : ℝ) / d|})

def PrefixValid {d t : ℕ} (x : Path t d) (b : ℕ) : Prop :=
  (∀ k : Fin t, k.val < b → ∃ y, x k = some y) ∧
  (∀ i j : Fin t, i.val < b → j.val < b → x i = x j → i = j)

def Free {d t : ℕ} (x : Path t d) (b : ℕ) (y : Fin d) : Prop :=
  ∀ k : Fin t, k.val < b → x k ≠ some y

noncomputable def availableMass {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (x : Path t d) (j : Fin t) (B : Finset (Fin d)) : ℝ :=
  ∑ y, if Free x j.val y ∧ y ∉ B then q j y else 0

/-- Draw the row law restricted to free, unreserved labels; fail on a stop
or an empty allowed support. -/
noncomputable def ordinaryWeight {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (x : Path t d) (j : Fin t) (B : Finset (Fin d)) (z : Option (Fin d)) : ℝ :=
  if PrefixValid x j.val ∧ trackingError q x j.val ≤ 1 / 20 ∧
      0 < availableMass q x j B then
    match z with
    | none => 0
    | some y => if Free x j.val y ∧ y ∉ B then
        q j y / availableMass q x j B else 0
  else if z = none then 1 else 0

noncomputable def sequentialWeight {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (x : Path t d) : ℝ := ∏ j, ordinaryWeight q x j ∅ (x j)

/-- All targets with queried steps strictly later than the ordinary step. -/
def pendingLabels {d t : ℕ} (S : Finset (Fin t)) (y : Fin t → Fin d)
    (j : Fin t) : Finset (Fin d) := (S.filter (fun i => j.val < i.val)).image y

noncomputable def forcingStepWeight {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (S : Finset (Fin t)) (y : Fin t → Fin d) (x : Path t d)
    (j : Fin t) (z : Option (Fin d)) : ℝ :=
  if j ∈ S then
    if PrefixValid x j.val ∧ trackingError q x j.val ≤ 1 / 20 ∧ Free x j.val (y j)
    then if z = some (y j) then 1 else 0
    else if z = none then 1 else 0
  else ordinaryWeight q x j (pendingLabels S y j) z

noncomputable def forcingWeight {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (S : Finset (Fin t)) (y : Fin t → Fin d) (x : Path t d) : ℝ :=
  ∏ j, forcingStepWeight q S y x j (x j)

/-- The two normalization nodes concern explicit triangular kernel products. -/
theorem sequential_weights_probability {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (hn : ∀ i y, 0 ≤ q i y) (hs : ∀ i, ∑ y, q i y = 1) :
    (∀ x, 0 ≤ sequentialWeight q x) ∧ (∑ x, sequentialWeight q x = 1) := by
  sorry

theorem forcing_weights_probability {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (hn : ∀ i y, 0 ≤ q i y) (hs : ∀ i, ∑ y, q i y = 1)
    (S : Finset (Fin t)) (y : Fin t → Fin d) :
    (∀ x, 0 ≤ forcingWeight q S y x) ∧ (∑ x, forcingWeight q S y x = 1) := by
  sorry

noncomputable def sequentialLaw {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (hn : ∀ i y, 0 ≤ q i y) (hs : ∀ i, ∑ y, q i y = 1) : FinProb (Path t d) :=
  ⟨sequentialWeight q, (sequential_weights_probability q hn hs).1,
    (sequential_weights_probability q hn hs).2⟩

noncomputable def forcingLaw {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (hn : ∀ i y, 0 ≤ q i y) (hs : ∀ i, ∑ y, q i y = 1)
    (S : Finset (Fin t)) (y : Fin t → Fin d) : FinProb (Path t d) :=
  ⟨forcingWeight q S y, (forcing_weights_probability q hn hs S y).1,
    (forcing_weights_probability q hn hs S y).2⟩

/-- `G` includes validity and the terminal time, and explicitly excludes stops. -/
def Good {d t : ℕ} (q : Fin t → Fin d → ℝ) (x : Path t d) : Prop :=
  PrefixValid x t ∧ trackingError q x t ≤ 1 / 20 ∧
    trackingError q x t ≤ (d : ℝ) ^ (-(0.1 : ℝ))

def RunningThrough {d t : ℕ} (q : Fin t → Fin d → ℝ) (x : Path t d) (b : ℕ) : Prop :=
  PrefixValid x b ∧ ∀ j : Fin t, j.val < b → trackingError q x j.val ≤ 1 / 20

noncomputable def failureBound (d : ℕ) : ℝ := Real.exp (-((d : ℝ) ^ (0.1 : ℝ)))
noncomputable def relativeError (d : ℕ) : ℝ := (d : ℝ) ^ (-(0.09 : ℝ))

def readLabels {d t : ℕ} (hd : 0 < d) (x : Path t d) : Fin t → Fin d :=
  fun i => (x i).getD ⟨0, hd⟩

noncomputable def conditionedLaw {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (h : OrderedInput d t q)
    (hG : 0 < (sequentialLaw q h.nonneg h.row_sum).pr (Good q)) :
    FinProb (Fin t → Fin d) :=
  FinProb.map (FinProb.cond (sequentialLaw q h.nonneg h.row_sum) (Good q) hG)
    (readLabels (by have := h.dimension; omega))

/-- Actual kernel drifts, including absorbing failure continuations. -/
noncomputable def stepDrift {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (x : Path t d) (a j : Fin t) : ℝ :=
  ∑ z, ordinaryWeight q x j ∅ z * z.elim 0 (q a)

noncomputable def forcedStepDrift {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (S : Finset (Fin t)) (y : Fin t → Fin d) (x : Path t d) (a j : Fin t) : ℝ :=
  ∑ z, forcingStepWeight q S y x j z * z.elim 0 (q a)

noncomputable def martingalePart {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (x : Path t d) (a : Fin t) (b : ℕ) : ℝ :=
  ∑ j : Fin t, if j.val < b then (x j).elim 0 (q a) - stepDrift q x a j else 0

noncomputable def forcedMartingalePart {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (S : Finset (Fin t)) (y : Fin t → Fin d) (x : Path t d) (a : Fin t) (b : ℕ) : ℝ :=
  ∑ j : Fin t, if j.val < b then
    (x j).elim 0 (q a) - forcedStepDrift q S y x a j else 0

def MartingaleGood {d t : ℕ} (q : Fin t → Fin d → ℝ) (x : Path t d) : Prop :=
  ∀ a (b : Fin (t + 1)), |martingalePart q x a b.val| ≤ (d : ℝ) ^ (-(1 / 8 : ℝ))

def ForcedMartingaleGood {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (S : Finset (Fin t)) (y : Fin t → Fin d) (x : Path t d) : Prop :=
  ∀ a (b : Fin (t + 1)),
    |forcedMartingalePart q S y x a b.val| ≤ (1 / 2 : ℝ) * (d : ℝ) ^ (-(1 / 8 : ℝ))

/-- TeX 03:662: free mass is `1-D`, bounded away from zero before a stop. -/
theorem free_mass_before_stop {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (h : OrderedInput d t q) (x : Path t d) (j : Fin t)
    (hv : PrefixValid x j.val) (he : trackingError q x j.val ≤ 1 / 20) :
    availableMass q x j ∅ = 1 - usedMass q x j j.val ∧
      1 / 5 ≤ availableMass q x j ∅ := by
  sorry

/-- TeX 03:663–668: exact drift and the bounded centered increment. -/
theorem sequential_drift_increment {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (h : OrderedInput d t q) (x : Path t d) (a j : Fin t)
    (hv : PrefixValid x j.val) (he : trackingError q x j.val ≤ 1 / 20) :
    stepDrift q x a j =
      (∑ y, if Free x j.val y then q a y * q j y else 0) /
        (1 - usedMass q x j j.val) ∧
    ∀ z, ordinaryWeight q x j ∅ z ≠ 0 →
      |z.elim 0 (q a) - stepDrift q x a j| ≤
        20 * (d : ℝ) ^ (-(0.95 : ℝ)) := by
  sorry

/-- TeX 03:668–671: simultaneous stopped martingale concentration. -/
theorem sequential_martingale_concentration :
    ∀ᶠ d : ℕ in atTop, ∀ t (q : Fin t → Fin d → ℝ) (h : OrderedInput d t q),
      1 - failureBound d ≤ (sequentialLaw q h.nonneg h.row_sum).pr (MartingaleGood q) := by
  sorry

/-- First summation by parts, TeX 03:673–680. -/
theorem drift_denominator_replacement : ∃ K : ℝ, 1 ≤ K ∧
    ∀ d t (q : Fin t → Fin d → ℝ), OrderedInput d t q →
      ∀ x a (b : Fin (t + 1)), RunningThrough q x b.val →
      |(∑ j : Fin t, if j.val < b.val then stepDrift q x a j else 0) -
        (∑ j : Fin t, if j.val < b.val then
          (∑ y, if Free x j.val y then q a y * q j y else 0) /
            (1 - (j.val : ℝ) / d) else 0)| ≤
        K * ((d : ℝ) ^ (-(1 / 8 : ℝ)) +
          (∑ j : Fin t, if j.val < b.val then trackingError q x j.val else 0) / d) := by
  sorry

/-- Second summation by parts, TeX 03:680–685. -/
theorem drift_column_replacement : ∃ K : ℝ, 1 ≤ K ∧
    ∀ d t (q : Fin t → Fin d → ℝ), OrderedInput d t q →
      ∀ x a (b : Fin (t + 1)), RunningThrough q x b.val →
      |(∑ j : Fin t, if j.val < b.val then
          (∑ y, if Free x j.val y then q a y * q j y else 0) /
            (1 - (j.val : ℝ) / d) else 0) -
        (∑ j : Fin t, if j.val < b.val then
          (1 - usedMass q x a j.val) / (1 - (j.val : ℝ) / d) else 0) / d| ≤
        K * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
  sorry

/-- TeX 03:687–689, including the first potential stopping index. -/
def DriftRecurrence {d t : ℕ} (q : Fin t → Fin d → ℝ) (K : ℝ) : Prop :=
  ∀ x (b : Fin (t + 1)), RunningThrough q x b.val → MartingaleGood q x →
    trackingError q x b.val ≤ K * (d : ℝ) ^ (-(1 / 8 : ℝ)) +
      K / d * ∑ j : Fin t, if j.val < b.val then trackingError q x j.val else 0

theorem tracking_drift_recurrence : ∃ K : ℝ, 1 ≤ K ∧
    ∀ d t (q : Fin t → Fin d → ℝ), OrderedInput d t q → DriftRecurrence q K := by
  sorry

/-- Scalar iteration isolated from the stochastic model, TeX 03:691. -/
theorem discrete_tracking_gronwall (n : ℕ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (e : Fin (n + 1) → ℝ) (hn : ∀ b, 0 ≤ e b)
    (hr : ∀ b, e b ≤ A + B * ∑ j : Fin (n + 1), if j.val < b.val then e j else 0) :
    ∀ b, e b ≤ A * Real.exp (B * b.val) := by
  sorry

/-- TeX 03:691–693: bootstrap the recurrence through a possible stop. -/
theorem tracking_bootstrap (K : ℝ) (hK : 1 ≤ K) :
    ∀ᶠ d : ℕ in atTop, ∀ t (q : Fin t → Fin d → ℝ), OrderedInput d t q →
      DriftRecurrence q K → ∀ x, sequentialWeight q x ≠ 0 → MartingaleGood q x → Good q x := by
  sorry

/-- Finite event transfer; avoids asserting that zero-weight paths are valid. -/
theorem tracking_probability_transfer {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (h : OrderedInput d t q)
    (hc : 1 - failureBound d ≤ (sequentialLaw q h.nonneg h.row_sum).pr (MartingaleGood q))
    (hb : ∀ x, sequentialWeight q x ≠ 0 → MartingaleGood q x → Good q x) :
    1 - failureBound d ≤ (sequentialLaw q h.nonneg h.row_sum).pr (Good q) := by
  sorry

end HypercubeRamsey.Injection
