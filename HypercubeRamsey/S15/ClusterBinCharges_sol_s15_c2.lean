import HypercubeRamsey.S15.ClusterBinTouch_sol_s15_c2

namespace HypercubeRamsey.Lane_sol_s15_c2

open HypercubeRamsey.S15 Classical
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def certificateCharge {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (c : CapacityCertificate PT) : ℝ :=
  if certificateActive PT hPT hm W c then
    (2 : ℝ) ^ c.2.2.card * ∏ g ∈ c.2.2, clusterBinProbability PT hPT hm W g c.1.2.1 else 0

theorem bin_probability_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (g : ClusterGroupIndex PT) (D : Finset (Fin (T.S.N k))) :
    0 ≤ clusterBinProbability PT hPT hm W g D := by
  unfold clusterBinProbability
  apply Finset.sum_nonneg
  intro D' hD'
  split_ifs
  · exact (clusterSolver PT hPT hm g.1.1).q_nonneg g.2 (historyOnSlice W g.1) D'
  · exact le_rfl

theorem certificate_touching_sum_eq {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (g : ClusterGroupIndex PT) :
    (∑ c : CapacityCertificate PT, if g ∈ c.2.2 then certificateCharge PT hPT hm W c else 0) =
      ∑ D : PhysicalBin PT, clusterBinProbability PT hPT hm W g D.2.1 *
        clusterPinnedCapacityCharge PT hPT hm W D.2.1 g := by
  classical
  let q := fun g D => clusterBinProbability PT hPT hm W g D
  have hfactor (A : Finset (ClusterGroupIndex PT)) (D : Finset (Fin (T.S.N k))) (hg : g ∈ A) :
      (2 : ℝ) ^ A.card * (∏ g' ∈ A, q g' D) =
      q g D * ((2 : ℝ) ^ A.card * ∏ g' ∈ A.erase g, q g' D) := by
    rw [← Finset.prod_erase_mul A (fun g' => q g' D) hg]
    ring
  have hterm (D : PhysicalBin PT) (y : Fin (T.S.N k)) (A : Finset (ClusterGroupIndex PT)) :
      (if g ∈ A then certificateCharge PT hPT hm W ⟨D, y, A⟩ else 0) =
      if y ∈ D.2.1 then q g D.2.1 *
        (if g ∈ A ∧ ∃ j, A ⊆ clusterCapacityBucket PT hPT hm W D.2.1 y j ∧
          A.card = clusterCertificateSize PT hPT hm W D.2.1 y j then
          (2 : ℝ) ^ A.card * ∏ g' ∈ A.erase g, q g' D.2.1 else 0) else 0 := by
    by_cases hg : g ∈ A <;> by_cases hy : y ∈ D.2.1 <;>
      by_cases he : ∃ j, A ⊆ clusterCapacityBucket PT hPT hm W D.2.1 y j ∧
        A.card = clusterCertificateSize PT hPT hm W D.2.1 y j
    all_goals simp only [certificateCharge, certificateActive, hg, hy, he,
      true_and, false_and, and_true, and_false, ite_true, ite_false, mul_zero]
    exact hfactor A D.2.1 hg
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro D hD
  have hsumy (y : Fin (T.S.N k)) :
      (∑ A : Finset (ClusterGroupIndex PT), if g ∈ A then certificateCharge PT hPT hm W ⟨D, y, A⟩ else 0) =
      if y ∈ D.2.1 then q g D.2.1 *
        (∑' j : ℕ, ∑ A ∈ (clusterCapacityBucket PT hPT hm W D.2.1 y j).powerset,
          if g ∈ A ∧ A.card = clusterCertificateSize PT hPT hm W D.2.1 y j then
            (2 : ℝ) ^ A.card * ∏ g' ∈ A.erase g, q g' D.2.1 else 0) else 0 := by
    simp_rw [hterm]
    by_cases hy : y ∈ D.2.1
    · simp only [if_pos hy]
      rw [← Finset.mul_sum]
      rw [pinned_column_certificate_sum]
    · simp only [if_neg hy, Finset.sum_const_zero]
  simp_rw [hsumy]
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  rfl

theorem certificate_touching_sum_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (g : ClusterGroupIndex PT) (ε : ℝ)
    (hpin : ∀ D : PhysicalBin PT, 0 < clusterBinProbability PT hPT hm W g D.2.1 →
      clusterPinnedCapacityCharge PT hPT hm W D.2.1 g ≤ ε) :
    (∑ c : CapacityCertificate PT, if g ∈ c.2.2 then certificateCharge PT hPT hm W c else 0) ≤ ε := by
  rw [certificate_touching_sum_eq]
  calc
    _ ≤ ∑ D : PhysicalBin PT, clusterBinProbability PT hPT hm W g D.2.1 * ε := by
      apply Finset.sum_le_sum
      intro D hD
      by_cases hp : 0 < clusterBinProbability PT hPT hm W g D.2.1
      · exact mul_le_mul_of_nonneg_left (hpin D hp) hp.le
      · have hz : clusterBinProbability PT hPT hm W g D.2.1 = 0 :=
          le_antisymm (le_of_not_gt hp) (bin_probability_nonneg PT hPT hm W g D.2.1)
        simp [hz]
    _ = ε := by rw [← Finset.sum_mul, physical_bin_probability_sum PT hPT hm W g, one_mul]

end HypercubeRamsey.Lane_sol_s15_c2
