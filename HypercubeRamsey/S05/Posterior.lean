import HypercubeRamsey.S05.Geometry

/-!
# D5.4 and L5.1c–d: raw order and predictive comparisons

The posterior statements use finite kernels.  Candidate values are re-sampled through every later kernel;
the raw order is part of the data rather than an implicit conditioning convention.
-/

namespace HypercubeRamsey

open Classical

/-- The raw dependency order `base → hidden columns → arrays`, with positions and tie data separate. -/
structure RawOrder5 (Base Hidden Arrays Clock : Type*)
    [Fintype Base] [Fintype Hidden] [Fintype Arrays] [Fintype Clock] where
  base : FinProb Base
  hidden : Base → FinProb Hidden
  arrays : Base → Hidden → FinProb Arrays
  clock : FinProb Clock

/-- The nested finite law for the parent/stream/hidden-column/array part of the experiment. -/
noncomputable def RawOrder5.raw {Base Hidden Arrays Clock : Type*}
    [Fintype Base] [Fintype Hidden] [Fintype Arrays] [Fintype Clock]
    (R : RawOrder5 Base Hidden Arrays Clock) : FinProb (Base × (Hidden × Arrays)) :=
  FinProb.bind R.base (fun b => FinProb.bind (R.hidden b) (fun h => R.arrays b h))

/-- Raw mass of a base-history value. -/
noncomputable def historyMass5 {Z H : Type*} [Fintype Z] [Fintype H]
    (P : FinProb (Z × H)) (h : H) : ℝ := ∑ z, P.w (z, h)

/-- The conditional prior on a candidate after the retained history. -/
noncomputable def priorAtHistory5 {Z H : Type*} [Fintype Z] [Fintype H]
    (P : FinProb (Z × H)) (h : H) (z : Z) : ℝ :=
  if historyMass5 P h = 0 then 0 else P.w (z, h) / historyMass5 P h

/-- The predictive density of a prefix under the retained history. -/
noncomputable def prefixMix5 {Z H W : Type*} [Fintype Z] [Fintype H] [Fintype W]
    (P : FinProb (Z × H)) (K : H → Z → FinProb W) (h : H) (w : W) : ℝ :=
  ∑ z, priorAtHistory5 P h z * (K h z).w w

/-- The posterior after the prefix. -/
noncomputable def prefixPosterior5 {Z H W : Type*} [Fintype Z] [Fintype H] [Fintype W]
    (P : FinProb (Z × H)) (K : H → Z → FinProb W) (h : H) (w : W) (z : Z) : ℝ :=
  if prefixMix5 P K h w = 0 then 0 else
    priorAtHistory5 P h z * (K h z).w w / prefixMix5 P K h w

/-- L5.1c: deleting one stream prefix changes the posterior by at most the reserved exponential factor,
outside a raw event of probability `exp(-δu)`. -/
theorem L5_1c_prefix_delete {Z H W : Type*} [Fintype Z] [Fintype H] [Fintype W]
    (P : FinProb (Z × H)) (K : H → Z → FinProb W) (Q : H → FinProb W)
    (a0 a1 delta u : ℝ) (hu : 0 < u) (hgap : a0 + delta ≤ a1)
    (hdom : ∀ h z w, (K h z).w w ≤ Real.exp (a0 * u) * (Q h).w w) :
    (∑ h, ∑ w, if prefixMix5 P K h w < Real.exp (-delta * u) * (Q h).w w
      then historyMass5 P h * prefixMix5 P K h w else 0) ≤ Real.exp (-delta * u) ∧
    (∀ h w, Real.exp (-delta * u) * (Q h).w w ≤ prefixMix5 P K h w →
      ∀ z, prefixPosterior5 P K h w z ≤
        Real.exp (a1 * u) * priorAtHistory5 P h z) := by
  sorry

/-- The finite gated block experiment used by Step 2. -/
structure BlockGate5 (Block Observation : Type*) [Fintype Block] [Fintype Observation] where
  prior : FinProb Block
  likelihood : Block → Observation → ℝ
  likelihood_nonneg : ∀ z t, 0 ≤ likelihood z t
  reference : FinProb Observation

/-- L5.1d's gated posterior estimate, with the block as candidate and the recorded hidden columns as data.

This is the Section 5 adapter for L3.7; likelihoods may be subprobabilities because the true-block gate is
retained. -/
theorem L5_1d_gated_block {Block Observation : Type*} [Fintype Block] [Fintype Observation]
    (M : BlockGate5 Block Observation) (ε s : ℝ) (hε : 0 < ε) :
    let m : Observation → ℝ := fun t => ∑ z, M.prior.w z * M.likelihood z t
    (∑ t, if m t < ε * M.reference.w t ∨ m t = 0 then m t else 0) ≤ ε ∧
    ((∀ z t, M.likelihood z t ≤ Real.exp s * M.reference.w t) →
      ∀ t, ¬ (m t < ε * M.reference.w t ∨ m t = 0) → ∀ z,
        M.prior.w z * M.likelihood z t / m t ≤ Real.exp s * ε⁻¹ * M.prior.w z) ∧
    (∀ h : Block → Observation → ℝ,
      ∑ t, m t * ∑ z, h z t * (M.prior.w z * M.likelihood z t / m t) =
        ∑ z, ∑ t, M.prior.w z * h z t * M.likelihood z t) := by
  exact gated_posterior M.prior M.likelihood M.likelihood_nonneg M.reference ε s hε

end HypercubeRamsey
