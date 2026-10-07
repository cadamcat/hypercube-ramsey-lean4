import Mathlib

/-!
# Hall interface

Fractional rows with column loads at most one give distinct representatives (Section 3, after Lemma 3.3).
-/

namespace HypercubeRamsey

theorem exists_injective_of_fractional {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (p : ι → Fin N → ℝ) (L : ι → Finset (Fin N))
    (hnonneg : ∀ v y, 0 ≤ p v y) (hsum : ∀ v, ∑ y, p v y = 1)
    (hsupp : ∀ v y, y ∉ L v → p v y = 0) (hload : ∀ y, ∑ v, p v y ≤ 1) :
    ∃ f : ι → Fin N, Function.Injective f ∧ ∀ v, f v ∈ L v := by
  classical
  refine (Finset.all_card_le_biUnion_card_iff_exists_injective L).mp ?_
  intro s
  let U := s.biUnion L
  have hmass : ∀ v ∈ s, ∑ y ∈ U, p v y = 1 := by
    intro v hv
    calc
      ∑ y ∈ U, p v y = ∑ y ∈ Finset.univ, p v y := by
        apply Finset.sum_subset (Finset.subset_univ U)
        intro y _ hy
        apply hsupp
        intro hmem
        exact hy (Finset.mem_biUnion.mpr ⟨v, hv, hmem⟩)
      _ = 1 := hsum v
  have hreal : (s.card : ℝ) ≤ (U.card : ℝ) := by
    calc
      (s.card : ℝ) = ∑ v ∈ s, (1 : ℝ) := by simp
      _ = ∑ v ∈ s, ∑ y ∈ U, p v y := by
        apply Finset.sum_congr rfl
        intro v hv
        exact (hmass v hv).symm
      _ = ∑ y ∈ U, ∑ v ∈ s, p v y := by rw [Finset.sum_comm]
      _ ≤ ∑ y ∈ U, (1 : ℝ) := Finset.sum_le_sum fun y hy => by
        calc
          ∑ v ∈ s, p v y ≤ ∑ v ∈ Finset.univ, p v y :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (by
              intro v _ _
              exact hnonneg v y)
          _ ≤ 1 := hload y
      _ = U.card := by simp [U]
  exact_mod_cast hreal

end HypercubeRamsey
