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
  classical
  have hmass_nonneg (h : H) : 0 ≤ historyMass5 P h := by
    unfold historyMass5
    exact Finset.sum_nonneg fun z _ => P.nonneg (z, h)
  have hprior_nonneg (h : H) (z : Z) : 0 ≤ priorAtHistory5 P h z := by
    unfold priorAtHistory5
    split_ifs with hh
    · exact le_rfl
    · exact div_nonneg (P.nonneg (z, h)) (le_of_lt (lt_of_le_of_ne (hmass_nonneg h) (Ne.symm hh)))
  have hmix_nonneg (h : H) (w : W) : 0 ≤ prefixMix5 P K h w := by
    unfold prefixMix5
    exact Finset.sum_nonneg fun z _ => mul_nonneg (hprior_nonneg h z) ((K h z).nonneg w)
  have hmass_sum : (∑ h, historyMass5 P h) = 1 := by
    unfold historyMass5
    rw [Finset.sum_comm]
    rw [← Fintype.sum_prod_type]
    exact P.sum_eq_one
  constructor
  · let c : ℝ := Real.exp (-delta * u)
    calc
      (∑ h, ∑ w, if prefixMix5 P K h w < c * (Q h).w w
          then historyMass5 P h * prefixMix5 P K h w else 0)
          ≤ ∑ h, ∑ w, historyMass5 P h * (c * (Q h).w w) := by
            apply Finset.sum_le_sum
            intro h hh
            apply Finset.sum_le_sum
            intro w hw
            by_cases hb : prefixMix5 P K h w < c * (Q h).w w
            · simp only [if_pos hb]
              exact mul_le_mul_of_nonneg_left (le_of_lt hb) (hmass_nonneg h)
            · simp only [if_neg hb]
              exact mul_nonneg (hmass_nonneg h)
                (mul_nonneg (le_of_lt (Real.exp_pos _)) ((Q h).nonneg w))
      _ = c := by
        calc
          (∑ h, ∑ w, historyMass5 P h * (c * (Q h).w w)) =
              ∑ h, historyMass5 P h * c := by
                apply Finset.sum_congr rfl
                intro h hh
                calc
                  (∑ w, historyMass5 P h * (c * (Q h).w w)) =
                      (historyMass5 P h * c) * (∑ w, (Q h).w w) := by
                        calc
                          (∑ w, historyMass5 P h * (c * (Q h).w w)) =
                              ∑ w, (historyMass5 P h * c) * (Q h).w w := by
                                apply Finset.sum_congr rfl
                                intro w hw
                                ring
                          _ = (historyMass5 P h * c) * (∑ w, (Q h).w w) := by
                                rw [← Finset.mul_sum]
                  _ = historyMass5 P h * c := by rw [(Q h).sum_eq_one, mul_one]
          _ = c := by
            rw [← Finset.sum_mul, hmass_sum]
            ring
      _ = Real.exp (-delta * u) := rfl
  · intro h w hthreshold z
    by_cases hm : prefixMix5 P K h w = 0
    · simp [prefixPosterior5, hm]
      exact mul_nonneg (le_of_lt (Real.exp_pos _)) (hprior_nonneg h z)
    · have hmix_pos : 0 < prefixMix5 P K h w := lt_of_le_of_ne (hmix_nonneg h w) (Ne.symm hm)
      have hexp_cancel : Real.exp (delta * u) * Real.exp (-delta * u) = 1 := by
        rw [← Real.exp_add]
        have hcancel : delta * u + (-delta) * u = 0 := by ring
        rw [hcancel, Real.exp_zero]
      have hQscaled : (Q h).w w ≤ Real.exp (delta * u) * prefixMix5 P K h w := by
        calc
          (Q h).w w = (Real.exp (delta * u) * Real.exp (-delta * u)) * (Q h).w w := by
            rw [hexp_cancel]
            ring
          _ = Real.exp (delta * u) * (Real.exp (-delta * u) * (Q h).w w) := by ring
          _ ≤ Real.exp (delta * u) * prefixMix5 P K h w :=
            mul_le_mul_of_nonneg_left hthreshold (le_of_lt (Real.exp_pos _))
      have hQratio : (Q h).w w / prefixMix5 P K h w ≤ Real.exp (delta * u) :=
        (div_le_iff₀ hmix_pos).2 hQscaled
      have hKratio : (K h z).w w / prefixMix5 P K h w ≤
          Real.exp (a0 * u) * Real.exp (delta * u) := by
        calc
          (K h z).w w / prefixMix5 P K h w ≤
              (Real.exp (a0 * u) * (Q h).w w) / prefixMix5 P K h w :=
                div_le_div_of_nonneg_right (hdom h z w) hmix_pos.le
          _ = Real.exp (a0 * u) * ((Q h).w w / prefixMix5 P K h w) := by ring
          _ ≤ Real.exp (a0 * u) * Real.exp (delta * u) :=
            mul_le_mul_of_nonneg_left hQratio (le_of_lt (Real.exp_pos _))
      have hexp_bound : Real.exp (a0 * u) * Real.exp (delta * u) ≤ Real.exp (a1 * u) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [hgap, hu]
      simp only [prefixPosterior5, hm]
      calc
        priorAtHistory5 P h z * (K h z).w w / prefixMix5 P K h w =
            priorAtHistory5 P h z * ((K h z).w w / prefixMix5 P K h w) := by ring
        _ ≤ priorAtHistory5 P h z * Real.exp (a1 * u) :=
          mul_le_mul_of_nonneg_left (le_trans hKratio hexp_bound) (hprior_nonneg h z)
        _ = Real.exp (a1 * u) * priorAtHistory5 P h z := by ring

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
