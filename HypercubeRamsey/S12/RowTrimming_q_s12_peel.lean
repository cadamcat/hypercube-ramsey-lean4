import HypercubeRamsey.S12.InteractionTails

namespace HypercubeRamsey.S12

open HypercubeRamsey
open scoped BigOperators

private theorem sum_eq_sum_support {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset α) (f : α → ℝ) (hf : ∀ x, x ∉ A → f x = 0) :
    ∑ x, f x = ∑ x ∈ A, f x := by
  classical
  exact (Finset.sum_subset (Finset.subset_univ A) (by
    intro x hx hxA
    exact hf x hxA)).symm

/-- Convert an unweighted pair sum on a finite set to expectation under its
uniform law. -/
theorem uniform_pair_sum {N : ℕ} (A : Finset (Fin N)) (hA : A.Nonempty)
    (p : Fin N → Fin N → Prop) (g : Fin N → Fin N → ℝ) [DecidableRel p] :
    (∑ x ∈ A, ∑ y ∈ A, if p x y then g x y else 0) =
      (A.card : ℝ) ^ 2 *
        (∑ x, ∑ y, if p x y then
          (Law.unif A hA).w x * (Law.unif A hA).w y * g x y else 0) := by
  classical
  let μ : Law N := Law.unif A hA
  let m : ℝ := A.card
  have hm : m ≠ 0 := by
    dsimp [m]
    exact_mod_cast (Finset.card_pos.mpr hA).ne'
  have hscale : (A.card : ℝ) ^ 2 * (m⁻¹ * m⁻¹) = 1 := by
    dsimp [m]
    have hcardne : (A.card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr hA).ne'
    field_simp
  have hμin : ∀ x ∈ A, μ.w x = m⁻¹ := by
    intro x hx
    simp [μ, m, Law.unif, FinProb.uniform, hx]
  have hμout : ∀ x, x ∉ A → μ.w x = 0 := by
    intro x hx
    simp [μ, Law.unif, FinProb.uniform, hx]
  have houter := sum_eq_sum_support A
    (fun x => ∑ y, if p x y then μ.w x * μ.w y * g x y else 0)
    (by
      intro x hx
      simp [hμout x hx])
  have hinner (x : Fin N) := sum_eq_sum_support A
    (fun y => if p x y then μ.w x * μ.w y * g x y else 0)
    (by
      intro y hy
      simp [hμout y hy])
  have hrestr :
      (∑ x, ∑ y, if p x y then μ.w x * μ.w y * g x y else 0) =
        ∑ x ∈ A, ∑ y ∈ A, if p x y then μ.w x * μ.w y * g x y else 0 := by
    rw [houter]
    apply Finset.sum_congr rfl
    intro x hx
    exact hinner x
  have hconst :
      (∑ x ∈ A, ∑ y ∈ A, if p x y then μ.w x * μ.w y * g x y else 0) =
        m⁻¹ * m⁻¹ * (∑ x ∈ A, ∑ y ∈ A, if p x y then g x y else 0) := by
    calc
      (∑ x ∈ A, ∑ y ∈ A, if p x y then μ.w x * μ.w y * g x y else 0) =
          ∑ x ∈ A, ∑ y ∈ A, (m⁻¹ * m⁻¹) * (if p x y then g x y else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        rw [hμin x hx, hμin y hy]
        by_cases hp : p x y <;> simp [hp] <;> ring
      _ = ∑ x ∈ A, (m⁻¹ * m⁻¹) *
          (∑ y ∈ A, if p x y then g x y else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [← Finset.mul_sum]
      _ = m⁻¹ * m⁻¹ * (∑ x ∈ A, ∑ y ∈ A, if p x y then g x y else 0) := by
        rw [← Finset.mul_sum]
  calc
    (∑ x ∈ A, ∑ y ∈ A, if p x y then g x y else 0) =
        (A.card : ℝ) ^ 2 * (m⁻¹ * m⁻¹ *
          (∑ x ∈ A, ∑ y ∈ A, if p x y then g x y else 0)) := by
      calc
        _ = 1 * (∑ x ∈ A, ∑ y ∈ A, if p x y then g x y else 0) := by simp
        _ = ((A.card : ℝ) ^ 2 * (m⁻¹ * m⁻¹)) *
            (∑ x ∈ A, ∑ y ∈ A, if p x y then g x y else 0) := by
          rw [← hscale]
        _ = _ := by ring_nf
    _ = (A.card : ℝ) ^ 2 *
        (∑ x, ∑ y, if p x y then μ.w x * μ.w y * g x y else 0) := by
      rw [hrestr, hconst]
    _ = (A.card : ℝ) ^ 2 *
        (∑ x, ∑ y, if p x y then
          (Law.unif A hA).w x * (Law.unif A hA).w y * g x y else 0) := by
      simp [μ]

/-- Finite Markov bound for a nonnegative function. -/
theorem filter_card_le_of_sum_bound {α : Type*} [DecidableEq α]
    (A : Finset α) (f : α → ℝ) (t B : ℝ) (ht : 0 < t)
    (hf : ∀ x ∈ A, 0 ≤ f x) (hB : (∑ x ∈ A, f x) ≤ B) :
    ((A.filter fun x => t < f x).card : ℝ) ≤ B / t := by
  classical
  let bad := A.filter fun x => t < f x
  have hlow : (bad.card : ℝ) * t ≤ ∑ x ∈ bad, f x := by
    calc
      (bad.card : ℝ) * t = ∑ x ∈ bad, t := by simp [mul_comm]
      _ ≤ ∑ x ∈ bad, f x := by
        apply Finset.sum_le_sum
        intro x hx
        exact le_of_lt (Finset.mem_filter.mp hx).2
  have hsub : (∑ x ∈ bad, f x) ≤ ∑ x ∈ A, f x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro x hx hxnot
    exact hf x hx
  apply (le_div_iff₀ ht).2
  calc
    ((A.filter fun x => t < f x).card : ℝ) * t = (bad.card : ℝ) * t := by rfl
    _ ≤ ∑ x ∈ bad, f x := hlow
    _ ≤ ∑ x ∈ A, f x := hsub
    _ ≤ B := hB

end HypercubeRamsey.S12
