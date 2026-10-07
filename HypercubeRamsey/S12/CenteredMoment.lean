import HypercubeRamsey.S12.CenteredMoment_q_s12_mom

/-!
# Heterogeneous centered moments
-/

namespace HypercubeRamsey.S12

open HypercubeRamsey
open Classical
open scoped BigOperators

/-- L12.2: the heterogeneous centered-moment expansion for arbitrary normalized finite weights. -/
theorem centered_moment_identity {N d u : ℕ}
    (τ : Fin N → ℝ) (hτ : ∑ x, τ x = 1)
    (π : Fin d → Fin N → ℝ) (hπ : ∀ l, ∑ y, π l y = 1)
    (φ : Fin d → Fin N → Fin N → ℝ) :
    ∑ ys : Fin d → Fin N,
        (∏ l, π l (ys l)) * ((∑ x, τ x * ∏ l, φ l x (ys l)) - 1) ^ u =
      ∑ xs : Fin u → Fin N,
        (∏ i, τ (xs i)) *
          ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
            ∏ l, ∑ y, π l y * ∏ i ∈ I, φ l (xs i) y := by
  classical
  have hcenter (ys : Fin d → Fin N) :
      (∑ x, τ x * ∏ l, φ l x (ys l)) - 1 =
        ∑ x, τ x * ((∏ l, φ l x (ys l)) - 1) := by
    calc
      (∑ x, τ x * ∏ l, φ l x (ys l)) - 1 =
          (∑ x, τ x * ∏ l, φ l x (ys l)) - ∑ x, τ x := by rw [← hτ]
      _ = ∑ x, (τ x * ∏ l, φ l x (ys l) - τ x) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ x, τ x * ((∏ l, φ l x (ys l)) - 1) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
  have hpow (ys : Fin d → Fin N) :
      ((∑ x, τ x * ∏ l, φ l x (ys l)) - 1) ^ u =
        ∑ xs : Fin u → Fin N, (∏ i, τ (xs i)) *
          ∏ i, ((∏ l, φ l (xs i) (ys l)) - 1) := by
    rw [hcenter ys, Fintype.sum_pow]
    congr 1
    ext xs
    rw [Finset.prod_mul_distrib]
  calc
    _ = ∑ ys : Fin d → Fin N, (∏ l, π l (ys l)) *
          ∑ xs : Fin u → Fin N, (∏ i, τ (xs i)) *
            ∏ i, ((∏ l, φ l (xs i) (ys l)) - 1) := by
        apply Finset.sum_congr rfl
        intro ys hys
        rw [hpow ys]
    _ = ∑ ys : Fin d → Fin N, ∑ xs : Fin u → Fin N,
          (∏ l, π l (ys l)) *
            ((∏ i, τ (xs i)) * ∏ i, ((∏ l, φ l (xs i) (ys l)) - 1)) := by
        apply Finset.sum_congr rfl
        intro ys hys
        change (∏ l, π l (ys l)) *
            ∑ xs ∈ (Finset.univ : Finset (Fin u → Fin N)),
              (∏ i, τ (xs i)) * ∏ i, ((∏ l, φ l (xs i) (ys l)) - 1) = _
        rw [Finset.mul_sum]
    _ = ∑ xs : Fin u → Fin N, ∑ ys : Fin d → Fin N,
          (∏ l, π l (ys l)) *
            ((∏ i, τ (xs i)) * ∏ i, ((∏ l, φ l (xs i) (ys l)) - 1)) := by
        change (∑ ys ∈ (Finset.univ : Finset (Fin d → Fin N)),
              ∑ xs ∈ (Finset.univ : Finset (Fin u → Fin N)),
                (∏ l, π l (ys l)) *
                  ((∏ i, τ (xs i)) * ∏ i, ((∏ l, φ l (xs i) (ys l)) - 1))) = _
        rw [Finset.sum_comm]
    _ = ∑ xs : Fin u → Fin N, (∏ i, τ (xs i)) *
          ∑ ys : Fin d → Fin N, (∏ l, π l (ys l)) *
            ∏ i, ((∏ l, φ l (xs i) (ys l)) - 1) := by
        apply Finset.sum_congr rfl
        intro xs hxs
        change (∑ ys ∈ (Finset.univ : Finset (Fin d → Fin N)), (∏ l, π l (ys l)) *
              ((∏ i, τ (xs i)) * ∏ i, ((∏ l, φ l (xs i) (ys l)) - 1))) =
            (∏ i, τ (xs i)) * ∑ ys ∈ (Finset.univ : Finset (Fin d → Fin N)),
              (∏ l, π l (ys l)) * ∏ i, ((∏ l, φ l (xs i) (ys l)) - 1)
        rw [Finset.univ.mul_sum]
        apply Finset.sum_congr rfl
        intro ys hys
        ring
    _ = ∑ xs : Fin u → Fin N, (∏ i, τ (xs i)) *
          ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
            ∏ l, ∑ y, π l y * ∏ i ∈ I, φ l (xs i) y := by
        apply Finset.sum_congr rfl
        intro xs hxs
        rw [weighted_product_sub_expand]

/-- L12.2b: expand one column into all interaction subsets; positive degrees also kill singleton terms. -/
theorem column_expansion {N d u : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Fin d → Fin N → ℝ) (xs : Fin u → Fin N) (I : Finset (Fin u))
    (hπ : ∀ l, ∑ y, π l y = 1)
    (hdeg : ∀ l i, i ∈ I → 0 < deg E c (π l) (xs i)) :
    ∀ l,
      ((∑ y, π l y * ∏ i ∈ I, (1 + acoef E c (π l) (xs i) y)) =
        ∑ J ∈ I.powerset, inter E c (π l) J xs) ∧
      (∀ i ∈ I, inter E c (π l) ({i} : Finset (Fin u)) xs = 0) := by
  classical
  intro l
  refine ⟨?_, ?_⟩
  · calc
      ∑ y, π l y * ∏ i ∈ I, (1 + acoef E c (π l) (xs i) y) =
          ∑ y, π l y * ∑ J ∈ I.powerset, ∏ i ∈ J, acoef E c (π l) (xs i) y := by
        apply Finset.sum_congr rfl
        intro y hy
        have hprod :
            ∏ i ∈ I, (1 + acoef E c (π l) (xs i) y) =
              ∏ i ∈ I, (acoef E c (π l) (xs i) y + 1) := by
          apply Finset.prod_congr rfl
          intro i hi
          ring
        rw [hprod, Finset.prod_add]
        simp
      _ = ∑ J ∈ I.powerset, ∑ y, π l y * ∏ i ∈ J, acoef E c (π l) (xs i) y := by
        calc
          ∑ y, π l y * ∑ J ∈ I.powerset, ∏ i ∈ J, acoef E c (π l) (xs i) y =
              ∑ y, ∑ J ∈ I.powerset, π l y * ∏ i ∈ J, acoef E c (π l) (xs i) y := by
            apply Finset.sum_congr rfl
            intro y hy
            rw [Finset.mul_sum]
          _ = ∑ J ∈ I.powerset, ∑ y, π l y * ∏ i ∈ J, acoef E c (π l) (xs i) y := by
            change (∑ y ∈ (Finset.univ : Finset (Fin N)),
                ∑ J ∈ I.powerset, π l y * ∏ i ∈ J, acoef E c (π l) (xs i) y) = _
            rw [Finset.sum_comm]
      _ = ∑ J ∈ I.powerset, inter E c (π l) J xs := by
        simp [inter]
  · intro i hi
    have hden : deg E c (π l) (xs i) ≠ 0 := ne_of_gt (hdeg l i hi)
    rw [inter]
    simp only [Finset.prod_singleton, acoef]
    calc
      ∑ y, π l y * (hit E c (xs i) y / deg E c (π l) (xs i) - 1) =
          ∑ y, ((π l y * hit E c (xs i) y) / deg E c (π l) (xs i) - π l y) := by
        apply Finset.sum_congr rfl
        intro y hy
        field_simp [hden] <;> ring
      _ = (∑ y, π l y * hit E c (xs i) y) / deg E c (π l) (xs i) - ∑ y, π l y := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_div]
      _ = 0 := by
        rw [show (∑ y, π l y * hit E c (xs i) y) = deg E c (π l) (xs i) by rfl,
          hπ l]
        simp [hden]

/-- L12.2: the two algebraic interfaces used by the moderate-moment estimate. -/
theorem centered_moment_export {N d u : ℕ}
    (τ : Fin N → ℝ) (hτ : ∑ x, τ x = 1)
    (π : Fin d → Fin N → ℝ) (hπ : ∀ l, ∑ y, π l y = 1)
    (φ : Fin d → Fin N → Fin N → ℝ)
    (E : Fin N → Fin N → Prop) (c : Colour)
    (xs : Fin u → Fin N) (I : Finset (Fin u))
    (hdeg : ∀ l i, i ∈ I → 0 < deg E c (π l) (xs i)) :
    (∑ ys : Fin d → Fin N,
        (∏ l, π l (ys l)) * ((∑ x, τ x * ∏ l, φ l x (ys l)) - 1) ^ u =
      ∑ xs : Fin u → Fin N,
        (∏ i, τ (xs i)) *
          ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
            ∏ l, ∑ y, π l y * ∏ i ∈ I, φ l (xs i) y) ∧
    (∀ l,
      ((∑ y, π l y * ∏ i ∈ I, (1 + acoef E c (π l) (xs i) y)) =
        ∑ J ∈ I.powerset, inter E c (π l) J xs) ∧
      (∀ i ∈ I, inter E c (π l) ({i} : Finset (Fin u)) xs = 0)) := by
  exact ⟨centered_moment_identity τ hτ π hπ φ,
    column_expansion E c π xs I hπ hdeg⟩

end HypercubeRamsey.S12
