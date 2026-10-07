import HypercubeRamsey.Framework.FinProb

/-!
# Lemma 3.7: gated posterior comparison

Source: `sections/03-…tex`, Lemma 3.7 (`lem:gated-posterior`) and its proof. Finite form: the candidate space
`Zc` and the data space `Dt` are finite; `F z t` is the likelihood of data `t` together with the required event
under candidate `z` (so it may have total mass below one); `Q` is any reference law on the data.
-/

namespace HypercubeRamsey

theorem gated_posterior {Zc Dt : Type*} [Fintype Zc] [Fintype Dt] (π : FinProb Zc)
    (F : Zc → Dt → ℝ) (hF0 : ∀ z t, 0 ≤ F z t) (Q : FinProb Dt) (ε s : ℝ) (hε : 0 < ε) :
    let m : Dt → ℝ := fun t => ∑ z, π.w z * F z t
    (∑ t, (if m t < ε * Q.w t ∨ m t = 0 then m t else 0)) ≤ ε ∧
    ((∀ z t, F z t ≤ Real.exp s * Q.w t) →
      ∀ t, ¬ (m t < ε * Q.w t ∨ m t = 0) → ∀ z, π.w z * F z t / m t ≤ Real.exp s * ε⁻¹ * π.w z) ∧
    (∀ h : Zc → Dt → ℝ, ∑ t, m t * ∑ z, h z t * (π.w z * F z t / m t) =
      ∑ z, ∑ t, π.w z * h z t * F z t) := by
  classical
  dsimp only
  let m : Dt → ℝ := fun t => ∑ z, π.w z * F z t
  change (∑ t, (if m t < ε * Q.w t ∨ m t = 0 then m t else 0) ≤ ε) ∧
    ((∀ z t, F z t ≤ Real.exp s * Q.w t) →
      ∀ t, ¬ (m t < ε * Q.w t ∨ m t = 0) →
        ∀ z, π.w z * F z t / m t ≤ Real.exp s * ε⁻¹ * π.w z) ∧
    (∀ h : Zc → Dt → ℝ, ∑ t, m t * ∑ z, h z t * (π.w z * F z t / m t) =
      ∑ z, ∑ t, π.w z * h z t * F z t)
  have hm_nonneg (t : Dt) : 0 ≤ m t := by
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg (π.nonneg z) (hF0 z t)
  have hterm_zero (t : Dt) (hm : m t = 0) (z : Zc) : π.w z * F z t = 0 := by
    have hle : π.w z * F z t ≤ m t := by
      unfold m
      exact Finset.single_le_sum
        (fun z' hz' => mul_nonneg (π.nonneg z') (hF0 z' t)) (Finset.mem_univ z)
    have hle0 : π.w z * F z t ≤ 0 := by simpa [hm] using hle
    exact le_antisymm hle0 (mul_nonneg (π.nonneg z) (hF0 z t))
  constructor
  · calc
      (∑ t, if m t < ε * Q.w t ∨ m t = 0 then m t else 0) ≤
          ∑ t, ε * Q.w t := by
            apply Finset.sum_le_sum
            intro t ht
            by_cases hbad : m t < ε * Q.w t ∨ m t = 0
            · rw [if_pos hbad]
              rcases hbad with hlt | hzero
              · exact le_of_lt hlt
              · rw [hzero]
                exact mul_nonneg hε.le (Q.nonneg t)
            · rw [if_neg hbad]
              exact mul_nonneg hε.le (Q.nonneg t)
      _ = ε * ∑ t, Q.w t := by rw [Finset.mul_sum]
      _ = ε := by rw [Q.sum_eq_one]; ring
  · constructor
    · intro hF t hgood z
      have hm_ne : m t ≠ 0 := by
        intro hz
        exact hgood (Or.inr hz)
      have hm_pos : 0 < m t := lt_of_le_of_ne (hm_nonneg t) (Ne.symm hm_ne)
      have hmass : ε * Q.w t ≤ m t := le_of_not_gt (fun hlt => hgood (Or.inl hlt))
      have hcoef : 0 ≤ Real.exp s * ε⁻¹ * π.w z :=
        mul_nonneg (mul_nonneg (le_of_lt (Real.exp_pos s)) (inv_nonneg.mpr hε.le))
          (π.nonneg z)
      have hden := mul_le_mul_of_nonneg_left hmass hcoef
      apply (div_le_iff₀ hm_pos).2
      calc
        π.w z * F z t ≤ π.w z * (Real.exp s * Q.w t) :=
          mul_le_mul_of_nonneg_left (hF z t) (π.nonneg z)
        _ = (Real.exp s * ε⁻¹ * π.w z) * (ε * Q.w t) := by
          field_simp [ne_of_gt hε]
          <;> ring
        _ ≤ (Real.exp s * ε⁻¹ * π.w z) * m t := hden
    · intro h
      calc
        (∑ t, m t * ∑ z, h z t * (π.w z * F z t / m t)) =
            ∑ t, ∑ z, m t * (h z t * (π.w z * F z t / m t)) := by
              apply Finset.sum_congr rfl
              intro t ht
              rw [Finset.mul_sum]
        _ = ∑ t, ∑ z, π.w z * h z t * F z t := by
              apply Finset.sum_congr rfl
              intro t ht
              apply Finset.sum_congr rfl
              intro z hz
              by_cases hm : m t = 0
              · calc
                  m t * (h z t * (π.w z * F z t / m t)) = 0 := by rw [hm]; ring
                  _ = π.w z * h z t * F z t := by
                    rw [show π.w z * h z t * F z t = h z t * (π.w z * F z t) by ring,
                      hterm_zero t hm z]
                    simp
              · field_simp [hm]
                <;> ring
        _ = ∑ z, ∑ t, π.w z * h z t * F z t := by rw [Finset.sum_comm]

end HypercubeRamsey
