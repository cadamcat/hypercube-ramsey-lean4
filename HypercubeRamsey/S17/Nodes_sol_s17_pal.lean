import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

namespace HypercubeRamsey.Lane_sol_s17_pal

open Classical
open scoped BigOperators

/-- Sum a typical-row bound and the own/crossing exceptional majorants. -/
theorem sum_pair_majorant {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P X : Finset α) (J : Finset β) (σ F W : α → ℝ) (C : β → α → ℝ)
    (s B mass tail : ℝ) (hPX : P ⊆ X) (hs : 0 ≤ s) (hB : 0 ≤ B)
    (hMass : (∑ z ∈ P, σ z) ≤ mass)
    (hW0 : ∀ z, 0 ≤ W z) (hW : (∑ z ∈ X, W z) ≤ tail)
    (hC0 : ∀ w z, 0 ≤ C w z) (hC : ∀ w ∈ J, (∑ z ∈ X, C w z) ≤ tail)
    (hPoint : ∀ z ∈ P, F z ≤ s * σ z + B * W z + B * ∑ w ∈ J, C w z) :
    (∑ z ∈ P, F z) ≤ s * mass + B * (1 + (J.card : ℝ)) * tail := by
  have hWP : (∑ z ∈ P, W z) ≤ tail := by
    apply le_trans _ hW
    exact Finset.sum_le_sum_of_subset_of_nonneg hPX (by intros; exact hW0 _)
  have hCP : (∑ z ∈ P, ∑ w ∈ J, C w z) ≤ (J.card : ℝ) * tail := by
    rw [Finset.sum_comm]
    calc
      (∑ w ∈ J, ∑ z ∈ P, C w z) ≤ ∑ w ∈ J, tail := by
        apply Finset.sum_le_sum
        intro w hw
        apply le_trans _ (hC w hw)
        exact Finset.sum_le_sum_of_subset_of_nonneg hPX (by intros; exact hC0 _ _)
      _ = (J.card : ℝ) * tail := by simp
  calc
    (∑ z ∈ P, F z) ≤ ∑ z ∈ P, (s * σ z + B * W z + B * ∑ w ∈ J, C w z) :=
      Finset.sum_le_sum hPoint
    _ = s * (∑ z ∈ P, σ z) + B * (∑ z ∈ P, W z) +
        B * (∑ z ∈ P, ∑ w ∈ J, C w z) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ s * mass + B * tail + B * ((J.card : ℝ) * tail) := by
      gcongr
    _ = s * mass + B * (1 + (J.card : ℝ)) * tail := by ring

end HypercubeRamsey.Lane_sol_s17_pal
