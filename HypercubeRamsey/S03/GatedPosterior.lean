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
      ∑ z, ∑ t, π.w z * h z t * F z t) := sorry

end HypercubeRamsey
