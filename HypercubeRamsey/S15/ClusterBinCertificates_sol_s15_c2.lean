import HypercubeRamsey.S15.Capacity
import HypercubeRamsey.S03.ConditionalAvoidance

namespace HypercubeRamsey.Lane_sol_s15_c2

open HypercubeRamsey.S15 Classical Filter
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

abbrev CapacityCertificate {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) :=
  (Σ i : Fin PT.tiling.m, Bin PT.tiling i) × Fin (T.S.N k) × Finset (ClusterGroupIndex PT)

noncomputable def certificateActive {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (c : CapacityCertificate PT) : Prop :=
  c.2.1 ∈ c.1.2.1 ∧ ∃ j,
    c.2.2 ⊆ clusterCapacityBucket PT hPT hm W c.1.2.1 c.2.1 j ∧
    c.2.2.card = clusterCertificateSize PT hPT hm W c.1.2.1 c.2.1 j

noncomputable def certificateEvent {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (c : CapacityCertificate PT)
    (B : ClusterBinAssignment PT) : Prop :=
  certificateActive PT hPT hm W c ∧ ∀ g ∈ c.2.2, (B g).1 = c.1.2.1

theorem certificate_active_nonempty {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    {W : ClusterHistory PT hPT hm} {c : CapacityCertificate PT}
    (hc : certificateActive PT hPT hm W c) : c.2.2.Nonempty := by
  obtain ⟨j, hsub, hcard⟩ := hc.2
  apply Finset.card_pos.mp
  rw [hcard]
  unfold clusterCertificateSize
  omega

theorem capacity_avoided_iff_certificates {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT) :
    clusterCapacityAvoided PT hPT hm W B ↔ ∀ c, ¬ certificateEvent PT hPT hm W c B := by
  constructor
  · intro h c hc
    obtain ⟨j, hsub, hcard⟩ := hc.1.2
    exact h c.1.1 c.1.2 c.2.1 hc.1.1 j c.2.2 hsub hcard hc.2
  · intro h i D y hy j A hsub hcard hchosen
    exact h ⟨⟨i, D⟩, y, A⟩ ⟨⟨hy, j, hsub, hcard⟩, hchosen⟩

theorem certificate_event_depends {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (c : CapacityCertificate PT)
    (B B' : ClusterBinAssignment PT) (hBB : ∀ g ∈ c.2.2, B g = B' g) :
    certificateEvent PT hPT hm W c B ↔ certificateEvent PT hPT hm W c B' := by
  unfold certificateEvent
  apply and_congr_right
  intro hactive
  apply forall₂_congr
  intro g hg
  rw [hBB g hg]

theorem bucket_width_succ {N : ℕ} (D : Finset (Fin N)) (j : ℕ) :
    clusterBucketWidth D (j + 1) = clusterBucketWidth D j / 2 := by
  unfold clusterBucketWidth
  simp only [zpow_neg, zpow_natCast, pow_succ]
  field_simp

theorem bucket_width_le_half {N : ℕ} (D : Finset (Fin N)) {j l : ℕ} (hjl : j < l) :
    clusterBucketWidth D l ≤ clusterBucketWidth D j / 2 := by
  rw [← bucket_width_succ]
  unfold clusterBucketWidth
  apply mul_le_mul_of_nonneg_left
  · exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem capacity_bucket_unique {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    {W : ClusterHistory PT hPT hm} {D : Finset (Fin (T.S.N k))} {y : Fin (T.S.N k)}
    {g : ClusterGroupIndex PT} {j l : ℕ}
    (hj : g ∈ clusterCapacityBucket PT hPT hm W D y j)
    (hl : g ∈ clusterCapacityBucket PT hPT hm W D y l) : j = l := by
  have hj' := (Finset.mem_filter.mp hj).2
  have hl' := (Finset.mem_filter.mp hl).2
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hwidth := bucket_width_le_half D hlt
    linarith only [hj'.1, hl'.2, hwidth]
  · have hwidth := bucket_width_le_half D hlt
    linarith only [hl'.1, hj'.2, hwidth]

theorem pinned_column_certificate_sum {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (D : Finset (Fin (T.S.N k)))
    (y : Fin (T.S.N k)) (g : ClusterGroupIndex PT) :
    (∑ A : Finset (ClusterGroupIndex PT),
      if g ∈ A ∧ ∃ j, A ⊆ clusterCapacityBucket PT hPT hm W D y j ∧
          A.card = clusterCertificateSize PT hPT hm W D y j then
        (2 : ℝ) ^ A.card * ∏ g' ∈ A.erase g, clusterBinProbability PT hPT hm W g' D else 0) =
    ∑' j : ℕ, ∑ A ∈ (clusterCapacityBucket PT hPT hm W D y j).powerset,
      if g ∈ A ∧ A.card = clusterCertificateSize PT hPT hm W D y j then
        (2 : ℝ) ^ A.card * ∏ g' ∈ A.erase g, clusterBinProbability PT hPT hm W g' D else 0 := by
  classical
  let bucket := fun j => clusterCapacityBucket PT hPT hm W D y j
  let size := fun j => clusterCertificateSize PT hPT hm W D y j
  let charge := fun A : Finset (ClusterGroupIndex PT) =>
    (2 : ℝ) ^ A.card * ∏ g' ∈ A.erase g, clusterBinProbability PT hPT hm W g' D
  by_cases hsome : ∃ j, g ∈ bucket j
  · obtain ⟨j, hj⟩ := hsome
    have hzero (l : ℕ) (hl : l ≠ j) :
        (∑ A ∈ (bucket l).powerset, if g ∈ A ∧ A.card = size l then charge A else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro A hA
      split_ifs with hc
      · have hgl : g ∈ bucket l := (Finset.mem_powerset.mp hA) hc.1
        have heq := capacity_bucket_unique hj hgl
        exact (hl heq.symm).elim
      · rfl
    have htsum : (∑' l : ℕ, ∑ A ∈ (bucket l).powerset,
        if g ∈ A ∧ A.card = size l then charge A else 0) =
        ∑ A ∈ (bucket j).powerset, if g ∈ A ∧ A.card = size j then charge A else 0 :=
      tsum_eq_single j hzero
    change (∑ A : Finset (ClusterGroupIndex PT),
      if g ∈ A ∧ ∃ l, A ⊆ bucket l ∧ A.card = size l then charge A else 0) = _
    rw [htsum]
    have hpred (A : Finset (ClusterGroupIndex PT)) :
        (g ∈ A ∧ ∃ l, A ⊆ bucket l ∧ A.card = size l) ↔
          A ∈ (bucket j).powerset ∧ g ∈ A ∧ A.card = size j := by
      constructor
      · rintro ⟨hg, l, hsub, hcard⟩
        have heq := capacity_bucket_unique hj (hsub hg)
        subst l
        exact ⟨Finset.mem_powerset.mpr hsub, hg, hcard⟩
      · rintro ⟨hA, hg, hcard⟩
        exact ⟨hg, j, Finset.mem_powerset.mp hA, hcard⟩
    calc
      _ = ∑ A : Finset (ClusterGroupIndex PT), if A ∈ (bucket j).powerset then
          (if g ∈ A ∧ A.card = size j then charge A else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro A hA
        by_cases hc : g ∈ A ∧ ∃ l, A ⊆ bucket l ∧ A.card = size l
        · have hp := hpred A |>.mp hc
          simp only [if_pos hc, if_pos hp.1, if_pos hp.2]
        · have hp := mt (hpred A).mpr hc
          split_ifs <;> simp_all
      _ = _ := Finset.sum_ite_mem_eq _ _
  · have hleft (A : Finset (ClusterGroupIndex PT)) :
        ¬ (g ∈ A ∧ ∃ l, A ⊆ bucket l ∧ A.card = size l) := by
      rintro ⟨hg, l, hsub, hcard⟩
      exact hsome ⟨l, hsub hg⟩
    have hzero (l : ℕ) :
        (∑ A ∈ (bucket l).powerset, if g ∈ A ∧ A.card = size l then charge A else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro A hA
      split_ifs with hc
      · exact (hsome ⟨l, (Finset.mem_powerset.mp hA) hc.1⟩).elim
      · rfl
    change (∑ A : Finset (ClusterGroupIndex PT),
      if g ∈ A ∧ ∃ l, A ⊆ bucket l ∧ A.card = size l then charge A else 0) =
      ∑' l : ℕ, ∑ A ∈ (bucket l).powerset, if g ∈ A ∧ A.card = size l then charge A else 0
    simp only [if_neg (hleft _), hzero, Finset.sum_const_zero, tsum_zero]

end HypercubeRamsey.Lane_sol_s15_c2
