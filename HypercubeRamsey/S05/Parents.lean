import HypercubeRamsey.S05.Parameters

/-!
# D5.2 and L5.1a: parents and stream segments

The parent prior interface is deliberately independent of the construction that supplies it.  A Section 6
caller can replace the parent sampling law while keeping the atom-cap hypotheses used by the later estimates.
-/

namespace HypercubeRamsey

open Classical

/-- A column is good for a tag when its colour degree is at least `0.95`. -/
def GoodColumn5 {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ : Law N) (y : Fin N) : Prop :=
  (95 : ℝ) / 100 ≤ colDeg E G μ y

/-- The tag mass for which two proposed parent labels are both good. -/
noncomputable def GoodPairMass5 {N : ℕ} {ι : Type*} [Fintype ι]
    (E : Fin N → Fin N → Prop) (G : Colour) (Λ : FinProb ι) (μ : ι → Law N)
    (y y' : Fin N) : ℝ :=
  ∑ i, if GoodColumn5 E G (μ i) y ∧ GoodColumn5 E G (μ i) y'
    then Λ.w i else 0

/-- Parent labels related at the `χ²/2` threshold. -/
def GoodParentPair5 {N : ℕ} {ι : Type*} [Fintype ι]
    (E : Fin N → Fin N → Prop) (G : Colour) (Λ : FinProb ι) (μ : ι → Law N)
    (χ : ℝ) (y y' : Fin N) : Prop :=
  χ ^ 2 / 2 ≤ GoodPairMass5 E G Λ μ y y'

/-- The parent system selected from the good-pair graph. -/
structure ParentSelection5 (N : ℕ) (Bin : Type*) [Fintype Bin] (χ : ℝ) where
  prior : ParentPrior5 N Bin
  prior_atom_constant : prior.atomConstant = 4 / χ ^ 2
  lab0 : Finset (Fin N)
  lab0_card : χ ^ 2 * N / 4 ≤ (lab0.card : ℝ)
  lab0_atom : ∀ y, y ∉ lab0 → prior.parent.w y = 0
  partnerCount_lower : ∀ v b, v ∈ lab0 → χ ^ 2 * N / 4 ≤
    (prior.partnerSet v b).card

/-- The marginal of one coordinate of a finite word law. -/
noncomputable def wordMarginal5 {N q : ℕ} (P : FinProb (Word5 N q)) (j : Fin q) (x : Fin N) : ℝ :=
  ∑ z, if z j = x then P.w z else 0

/-- One raw stream segment and its unconditioned product reference law. -/
structure StreamSegments5 (n N q : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
    (γ K' a₀ : ℝ) where
  paired : Fin N → Fin N → Prop
  segment : Fin N → Fin N → FinProb (Word5 N q)
  reference : FinProb (Word5 N q)
  segment_density : ∀ x y z, paired x y →
    (segment x y).w z ≤ Real.exp (a₀ * q) * reference.w z
  segment_hits : ∀ x y z, paired x y → (segment x y).w z ≠ 0 →
    ∀ j, Hits E G (z j) x ∧ Hits E G (z j) y
  reference_coordinate_cap : ∀ j x,
    wordMarginal5 reference j x ≤ K' / N
  reference_density : ∀ z,
    reference.w z ≤ Real.exp ((q : ℝ) * (n : ℝ) ^ γ) / (N : ℝ) ^ q

/-- L5.1a: the good-pair construction gives parent atoms, partner sets, and stream-segment bounds.

Only positive-mass tags need satisfy the width and good-column hypotheses; this is the one-shot convention
used by Part B. -/
theorem L5_1a (γ K' χ : ℝ) {n N : ℕ} {ι Bin : Type*} [Fintype ι] [Fintype Bin]
    (p : Params5 γ K' χ) (E : Fin N → Fin N → Prop) (G : Colour)
    (Λ : FinProb ι) (μ : ι → Law N) (hN : 0 < N)
    (hwidth : ∀ i, 0 < Λ.w i → (μ i).WidthLE ((n : ℝ) ^ γ))
    (hbalance : ∀ x, (N : ℝ) * ∑ i, Λ.w i * (μ i).w x ≤ K')
    (hgood : ∀ i, 0 < Λ.w i → χ * N ≤
      ((Finset.univ.filter (fun y => GoodColumn5 E G (μ i) y)).card : ℝ)) :
    ∃ P : ParentSelection5 N Bin χ,
      ∃ S : StreamSegments5 n N p.q0 E G γ K' (p.a 0),
        (∀ v ∈ P.lab0, ∀ b,
          P.prior.partnerSet v b =
            Finset.univ.filter (GoodParentPair5 E G Λ μ χ v)) ∧
        (∀ x y, S.paired x y ↔ GoodParentPair5 E G Λ μ χ x y) := by
  sorry

end HypercubeRamsey
