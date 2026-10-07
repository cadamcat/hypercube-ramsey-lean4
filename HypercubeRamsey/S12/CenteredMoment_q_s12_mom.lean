import HypercubeRamsey.S12.Defs

namespace HypercubeRamsey.S12

open Classical
open scoped BigOperators

theorem prod_sub_one_expand {ι : Type*} [Fintype ι] (P : ι → ℝ) :
    ∏ i, (P i - 1) =
      ∑ I : Finset ι, (-1 : ℝ) ^ (Fintype.card ι - I.card) * ∏ i ∈ I, P i := by
  classical
  rw [show (fun i => P i - 1) = (fun i => P i + (-1)) by funext i; ring]
  rw [Finset.prod_add]
  simp [Finset.card_sdiff_of_subset]
  apply Finset.sum_congr rfl
  intro I hI
  ring

theorem weighted_product_sub_expand {N d u : ℕ}
    (π : Fin d → Fin N → ℝ) (φ : Fin d → Fin N → Fin N → ℝ)
    (xs : Fin u → Fin N) :
    ∑ ys : Fin d → Fin N, (∏ l, π l (ys l)) *
        ∏ i, ((∏ l, φ l (xs i) (ys l)) - 1) =
      ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
        ∏ l, ∑ y, π l y * ∏ i ∈ I, φ l (xs i) y := by
  classical
  have hexpand (ys : Fin d → Fin N) :
      ∏ i, ((∏ l, φ l (xs i) (ys l)) - 1) =
        ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
          ∏ i ∈ I, ∏ l, φ l (xs i) (ys l) := by
    simpa using prod_sub_one_expand
      (fun i : Fin u => ∏ l, φ l (xs i) (ys l))
  calc
    _ = ∑ ys : Fin d → Fin N, (∏ l, π l (ys l)) *
          ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
            ∏ i ∈ I, ∏ l, φ l (xs i) (ys l) := by
        congr 1
        funext ys
        rw [hexpand ys]
    _ = ∑ ys : Fin d → Fin N, ∑ I : Finset (Fin u),
          (∏ l, π l (ys l)) *
            ((-1 : ℝ) ^ (u - I.card) * ∏ i ∈ I, ∏ l, φ l (xs i) (ys l)) := by
        apply Finset.sum_congr rfl
        intro ys hys
        change (∏ l, π l (ys l)) *
            (∑ I ∈ Finset.univ, (-1 : ℝ) ^ (u - I.card) *
              ∏ i ∈ I, ∏ l, φ l (xs i) (ys l)) = _
        rw [Finset.mul_sum]
    _ = ∑ I : Finset (Fin u), ∑ ys : Fin d → Fin N,
          (∏ l, π l (ys l)) *
            ((-1 : ℝ) ^ (u - I.card) * ∏ i ∈ I, ∏ l, φ l (xs i) (ys l)) := by
        change (∑ ys ∈ (Finset.univ : Finset (Fin d → Fin N)),
            ∑ I ∈ (Finset.univ : Finset (Finset (Fin u))),
            (∏ l, π l (ys l)) *
              ((-1 : ℝ) ^ (u - I.card) * ∏ i ∈ I, ∏ l, φ l (xs i) (ys l))) = _
        rw [Finset.sum_comm]
    _ = ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
          ∑ ys : Fin d → Fin N, (∏ l, π l (ys l)) *
            ∏ i ∈ I, ∏ l, φ l (xs i) (ys l) := by
        apply Finset.sum_congr rfl
        intro I hI
        change (∑ ys ∈ (Finset.univ : Finset (Fin d → Fin N)),
              (∏ l, π l (ys l)) *
              ((-1 : ℝ) ^ (u - I.card) * ∏ i ∈ I, ∏ l, φ l (xs i) (ys l))) =
            (-1 : ℝ) ^ (u - I.card) *
              ∑ ys ∈ (Finset.univ : Finset (Fin d → Fin N)), (∏ l, π l (ys l)) *
                ∏ i ∈ I, ∏ l, φ l (xs i) (ys l)
        rw [Finset.univ.mul_sum]
        apply Finset.sum_congr rfl
        intro ys hys
        ring
    _ = ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
          ∏ l, ∑ y, π l y * ∏ i ∈ I, φ l (xs i) y := by
        congr 1
        ext I
        congr 1
        calc
          ∑ ys : Fin d → Fin N, (∏ l, π l (ys l)) *
              ∏ i ∈ I, ∏ l, φ l (xs i) (ys l) =
            ∑ ys : Fin d → Fin N, ∏ l,
              (π l (ys l) * ∏ i ∈ I, φ l (xs i) (ys l)) := by
                congr 1
                funext ys
                rw [Finset.prod_comm]
                rw [← Finset.prod_mul_distrib]
          _ = ∏ l, ∑ y, π l y * ∏ i ∈ I, φ l (xs i) y := by
                symm
                exact Fintype.prod_sum
                  (fun l : Fin d => fun y : Fin N => π l y * ∏ i ∈ I, φ l (xs i) y)

end HypercubeRamsey.S12
