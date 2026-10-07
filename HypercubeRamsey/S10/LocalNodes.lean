import HypercubeRamsey.S10.FixedList
import HypercubeRamsey.S03.GatedPosterior

/-!
# Section 10 local nodes

Reusable quantitative and finite-probability interfaces for the steps between the
fixed-list test and the tag/embedding construction. -/

namespace HypercubeRamsey.S10

open scoped BigOperators
open Classical Filter

/-- P10.1b (10:43–54): the scale inequalities needed for the tuple-array, fan and
height bounds. The four exponents are those used in the paper's choice of `m`, `k`
and `T`; all inequalities hold eventually under the stated parameter range. -/
theorem p10_1b_scale_separation
    (η₀ ζ δ : ℝ) (hη₀ : 0 < η₀) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) :
    ∀ᶠ n : ℕ in atTop,
      4 * (n : ℝ) ^ (500 * δ) < (n : ℝ) ^ η₀ ∧
      3 * (n : ℝ) ^ (500 * δ) < (n : ℝ) ^ ζ ∧
      4 * (n : ℝ) ^ (200 * δ) < (n : ℝ) ^ (1 - δ) ∧
      ((n : ℝ) ^ (200 * δ) + (n : ℝ) ^ (141 * δ)) * Real.log n <
        (n : ℝ) ^ (298 * δ) := by
  sorry

/-- P10.1d (10:101–126): generic union bound for `n` disjoint failed lists chosen
from a finite menu. The premise is the product estimate supplied by independence of
the tuple arrays on disjoint lists. -/
theorem p10_1d_disjoint_failure_union_bound
    {Ω : Type*} [Fintype Ω] {L n : ℕ} (P : FinProb Ω)
    (failed : Fin L → Ω → Prop) (p : ℝ)
    (hp : 0 ≤ p)
    (hproduct : ∀ f : Fin n → Fin L,
      P.pr (fun ω => ∀ i, failed (f i) ω) ≤ p ^ n) :
    P.pr (fun ω => ∃ f : Fin n → Fin L, ∀ i, failed (f i) ω) ≤
      (L : ℝ) ^ n * p ^ n := by
  sorry

/-- Squared-tilt mass of deletion-ratio failures. -/
noncomputable def squaredTiltBadWeight {q : ℕ} (ρ : FinProb (Fin q))
    (mass massWithout : Fin q → ℝ) (t : ℝ) : ℝ := by
  classical
  exact ∑ j : Fin q,
    if mass j / massWithout j < t then ρ.w j * (mass j) ^ 2 else 0

/-- P10.1e (10:128–149): the squared tilt assigns at most
`t² A(F₋c) / A(F)` mass to clusters whose deletion ratio is below `t`. -/
theorem p10_1e_squared_tilt_tail_bound
    {q : ℕ} (ρ : FinProb (Fin q)) (mass massWithout : Fin q → ℝ) (t : ℝ)
    (hρ : ∀ j, 0 ≤ ρ.w j)
    (hmass : ∀ j, 0 ≤ mass j ∧ 0 ≤ massWithout j ∧ mass j ≤ massWithout j)
    (ht : 0 ≤ t) :
    squaredTiltBadWeight ρ mass massWithout t /
      (∑ j : Fin q, ρ.w j * (mass j) ^ 2) ≤
        t ^ 2 * (∑ j : Fin q, ρ.w j * (massWithout j) ^ 2) /
          (∑ j : Fin q, ρ.w j * (mass j) ^ 2) := by
  sorry

/-- Sum of all mask prices against a cluster aggregate. -/
def totalMaskPrice {N T : ℕ} (ν : Law N) (price : Fin (T + 1) → Fin N → ℝ) : ℝ :=
  ∑ t : Fin (T + 1), ∑ y : Fin N, ν.w y * price t y

/-- Labels whose total price over all own-list sizes is cheap. -/
noncomputable def cheapMaskLabels {N T : ℕ} (ν : Law N)
    (price : Fin (T + 1) → Fin N → ℝ) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun y =>
    (∑ t : Fin (T + 1), price t y) ≤ 10 * totalMaskPrice ν price

/-- P10.1f (10:153): a cheap-label mask retains at least nine tenths of the
aggregate and bounds every own-list price. -/
theorem p10_1f_mask_price_separation
    {N T : ℕ} (ν : Law N) (price : Fin (T + 1) → Fin N → ℝ)
    (hprice : ∀ t y, 0 ≤ price t y) :
    9 / 10 ≤ lawMassOn ν (cheapMaskLabels ν price) ∧
    ∀ t : Fin (T + 1),
      (∑ y ∈ cheapMaskLabels ν price, ν.w y * price t y) ≤
        10 * totalMaskPrice ν price := by
  sorry

/-- P10.1g (10:155–186): transfer a pointwise comparison with the aggregate law to
the required normalized pointwise row cap. -/
theorem p10_1g_prescribed_list_to_selection
    {N : ℕ} (m : ℕ) (ν : Law N) (pHat : Fin N → ℝ) (B : ℝ)
    (hrow : ∀ y, pHat y ≤ B * ν.w y)
    (hcap : ∀ y, (N : ℝ) * B * ν.w y ≤ Real.exp ((1 / 10 : ℝ) * m)) :
    ∀ y, (N : ℝ) * pHat y ≤ Real.exp ((1 / 10 : ℝ) * m) := by
  intro y
  calc
    (N : ℝ) * pHat y ≤ (N : ℝ) * (B * ν.w y) :=
      mul_le_mul_of_nonneg_left (hrow y) (Nat.cast_nonneg N)
    _ = (N : ℝ) * B * ν.w y := by ring
    _ ≤ Real.exp ((1 / 10 : ℝ) * m) := hcap y

/-- P10.1h (10:191–222): multiply per-group likelihood comparisons into a
comparison for the full odd-neighbor star. -/
theorem p10_1h_product_likelihood_comparison
    {A B : Type*} [Fintype A] [Fintype B] {m : ℕ}
    (L Q : Fin m → A → B → ℝ) (s : Fin m → ℝ)
    (hQ : ∀ i a b, 0 ≤ Q i a b)
    (hcompare : ∀ i a b, L i a b ≤ Real.exp (s i) * Q i a b) :
    ∀ a b, (∏ i : Fin m, L i a b) ≤
      Real.exp (∑ i : Fin m, s i) * ∏ i : Fin m, Q i a b := by
  sorry

/-- P10.1i (10:224–262): predictive gated posterior bound, including the small-data
exception, posterior domination and the exact integration identity. -/
theorem p10_1i_predictive_test
    {Zc Dt : Type*} [Fintype Zc] [Fintype Dt] (π : FinProb Zc)
    (F : Zc → Dt → ℝ) (hF0 : ∀ z t, 0 ≤ F z t) (Q : FinProb Dt)
    (ε s : ℝ) (hε : 0 < ε) :
    let m : Dt → ℝ := fun t => ∑ z, π.w z * F z t
    (∑ t, (if m t < ε * Q.w t ∨ m t = 0 then m t else 0)) ≤ ε ∧
    ((∀ z t, F z t ≤ Real.exp s * Q.w t) →
      ∀ t, ¬ (m t < ε * Q.w t ∨ m t = 0) → ∀ z,
        π.w z * F z t / m t ≤ Real.exp s * ε⁻¹ * π.w z) ∧
    (∀ h : Zc → Dt → ℝ,
      ∑ t, m t * ∑ z, h z t * (π.w z * F z t / m t) =
        ∑ z, ∑ t, π.w z * h z t * F z t) := by
  exact HypercubeRamsey.gated_posterior π F hF0 Q ε s hε

end HypercubeRamsey.S10
