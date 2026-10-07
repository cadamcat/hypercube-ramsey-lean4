import HypercubeRamsey.S15.ClusterSeparation_sol_s15_transfer
import HypercubeRamsey.S15.ClusterBinReverse_sol_s15_transfer

namespace HypercubeRamsey.Lane_sol_s15_transfer

open Classical S15 Filter OAI.HypercubeRamsey
open scoped BigOperators

noncomputable def rowCoreWords {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) : Finset (ClusterConsultation PT) :=
  rowWordQueries PT hPT hm a ∪ (clusterBulkNeighbours PT hPT a).image (wordAtOdd PT hPT hm)

noncomputable def coreRowProduct {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (a : EvenPosition T k)
    (W : ClusterHistory PT hPT hm) (I : ClusterInternalData PT) : ℝ :=
  (PT.tiling.P i).M * clusterSigma PT hPT hm W I a x *
    ∏ b ∈ clusterBulkNeighbours PT hPT a,
      normalizedHit (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT b.1)) x
        (clusterLabelFromInternal (hPT := hPT) hm I b)

noncomputable def coreSingleMask {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k)
    (r : Fin (T.S.n k)) : ClusterMask PT :=
  let base : ClusterMask PT := ⟨fun _ => a, Finset.univ.erase r, ∅, ∅⟩
  {base with crossingBins := clusterAllowedCrossings PT hPT base}

theorem core_single_kept_rows {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k) (r : Fin (T.S.n k)) :
    clusterKeptRows (coreSingleMask PT hPT a r) = {r} := by
  ext t
  simp [clusterKeptRows, coreSingleMask]

theorem core_single_crossings_empty {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k) (r : Fin (T.S.n k)) :
    clusterAllowedCrossings PT hPT (coreSingleMask PT hPT a r) \
      (coreSingleMask PT hPT a r).crossingBins = ∅ := by
  change clusterAllowedCrossings PT hPT (⟨fun _ => a, Finset.univ.erase r, ∅, ∅⟩ : ClusterMask PT) \
      clusterAllowedCrossings PT hPT (⟨fun _ => a, Finset.univ.erase r, ∅, ∅⟩ : ClusterMask PT) = ∅
  exact Finset.sdiff_self _

theorem core_single_product {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (a : EvenPosition T k) (r : Fin (T.S.n k))
    (W : ClusterHistory PT hPT hm) (I : ClusterInternalData PT) :
    clusterKeptProduct PT hPT hm i x (coreSingleMask PT hPT a r) W I =
      coreRowProduct PT hPT hm i x a W I := by
  unfold clusterKeptProduct
  rw [core_single_kept_rows, core_single_crossings_empty]
  simp only [Finset.prod_singleton, Finset.prod_empty, mul_one]
  rfl

theorem core_single_product_fun {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (a : EvenPosition T k) (r : Fin (T.S.n k))
    (W : ClusterHistory PT hPT hm) :
    clusterKeptProduct PT hPT hm i x (coreSingleMask PT hPT a r) W =
      coreRowProduct PT hPT hm i x a W := by
  funext I
  exact core_single_product PT hPT hm i x a r W I

theorem core_single_word_queries {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) (r : Fin (T.S.n k)) :
    keptWordQueries PT hPT hm (coreSingleMask PT hPT a r) = rowCoreWords PT hPT hm a := by
  unfold keptWordQueries
  rw [core_single_kept_rows, core_single_crossings_empty]
  simp only [Finset.singleton_biUnion, Finset.image_empty, Finset.union_empty]
  rfl

theorem row_core_word_groups_subset {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) :
    (rowCoreWords PT hPT hm a).image (wordGroup PT hPT hm) ⊆ clusterCoreGroups PT hPT hm a := by
  intro g hg
  obtain ⟨c, hc, hcg⟩ := Finset.mem_image.mp hg
  subst g
  rcases Finset.mem_union.mp hc with hc | hc
  · exact row_word_group_mem_core PT hPT hm a hc
  · obtain ⟨b, hb, hbc⟩ := Finset.mem_image.mp hc
    rw [← hbc]
    have hp := (Finset.mem_filter.mp hb).2
    exact Lane_q_s15_c2.clusterGroupIndexAt_mem_coreGroups a b hp.1 hp.2.1

theorem consultation_scope_mono {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    {U V : Finset (ClusterConsultation PT)} (hUV : U ⊆ V) :
    clusterConsultationScope PT hPT hm U ⊆ clusterConsultationScope PT hPT hm V := by
  intro r hr
  obtain ⟨c, hc, e, hd⟩ := (Finset.mem_filter.mp hr).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, c, hUV hc, e, hd⟩

theorem core_single_reference_scope_subset {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) (r : Fin (T.S.n k)) :
    clusterConsultationScope PT hPT hm (referenceConsultations PT hPT hm (coreSingleMask PT hPT a r)) ⊆
      coreRecordFootprint PT hPT hm a := by
  apply Finset.Subset.trans _ (core_consultations_scope_subset PT hPT hm a)
  apply consultation_scope_mono
  intro c hc
  change c ∈ ((clusterKeptRows (coreSingleMask PT hPT a r)).image
      (fun t => rowConsultation PT hPT hm ((coreSingleMask PT hPT a r).positions t))) ∪
    (((keptWordQueries PT hPT hm (coreSingleMask PT hPT a r)).image (wordGroup PT hPT hm)).image
      groupConsultation) at hc
  rw [core_single_kept_rows, core_single_word_queries] at hc
  rcases Finset.mem_union.mp hc with hc | hc
  · obtain ⟨t, ht, htc⟩ := Finset.mem_image.mp hc
    exact Finset.mem_union_left _ (Finset.mem_singleton.mpr htc.symm)
  · obtain ⟨g, hg, hgc⟩ := Finset.mem_image.mp hc
    exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨g, row_core_word_groups_subset PT hPT hm a hg, hgc⟩)

theorem core_row_word_depends {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (a : EvenPosition T k) (r : Fin (T.S.n k))
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT) :
    FinProb.DependsOn (fun ys => coreRowProduct PT hPT hm i x a W (internalOfWordLabels B ys))
      (rowCoreWords PT hPT hm a) := by
  have h := kept_product_word_depends PT hPT hm i x (coreSingleMask PT hPT a r) W B
  simp_rw [core_single_product, core_single_word_queries] at h
  exact h

theorem core_row_bin_depends {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (a : EvenPosition T k) (r : Fin (T.S.n k))
    (W : ClusterHistory PT hPT hm) :
    ClusterBinDependsOn (fun B => (clusterIndependentLabelKernel PT hPT hm W B).E
      (coreRowProduct PT hPT hm i x a W)) (clusterCoreGroups PT hPT hm a) := by
  have h := kept_label_integral_bin_depends PT hPT hm i x (coreSingleMask PT hPT a r) W
  simp_rw [core_single_product_fun, core_single_word_queries] at h
  intro B B' hBB
  apply h
  intro g hg
  exact hBB g (row_core_word_groups_subset PT hPT hm a hg)

theorem core_row_history_depends {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (a : EvenPosition T k) (r : Fin (T.S.n k)) :
    ClusterHistoryDependsOn (fun W => (clusterIndependentBinKernel PT hPT hm W).E
      (fun B => (clusterIndependentLabelKernel PT hPT hm W B).E (coreRowProduct PT hPT hm i x a W)))
      (coreRecordFootprint PT hPT hm a) := by
  have h := reference_mean_history_depends PT hPT hm i x (coreSingleMask PT hPT a r)
  unfold clusterReferenceMean at h
  simp_rw [core_single_product_fun] at h
  intro W W' hWW
  apply h
  intro g hg
  exact hWW g (core_single_reference_scope_subset PT hPT hm a r hg)

theorem raw_reference_E_eq_stages {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (F : ClusterHistory PT hPT hm × ClusterInternalData PT → ℝ) :
    (clusterRawReferenceLaw PT hPT hm).E F =
      (clusterHistoryLaw PT hPT hm).E (fun W =>
        (FinLaw.pi (binLawAt PT hPT hm W)).E (fun B =>
          (FinLaw.pi (wordLabelLaw PT hPT hm W B)).E
            (fun ys => F (W, internalOfWordLabels B ys)))) := by
  rw [clusterRawReferenceLaw, Lane_q_s15_c3.finLaw_bind_E]
  apply congrArg (FinLaw.E (clusterHistoryLaw PT hPT hm))
  funext W
  rw [internal_kernel_eq_bin_label_E]
  apply congrArg (FinLaw.E (FinLaw.pi (binLawAt PT hPT hm W)))
  funext B
  exact independent_label_E_eq_word_E PT hPT hm W B _

theorem raw_core_rows_factor {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (M : ClusterMask PT)
    (hM : ClusterMaskGeometry PT hPT i M)
    (hradius : (1 : ℝ) ≤ κ.ρ * (PT.tiling.P i).h) :
    (clusterRawReferenceLaw PT hPT hm).E (fun z =>
      ∏ r ∈ clusterKeptRows M, coreRowProduct PT hPT hm i x (M.positions r) z.1 z.2) =
      ∏ r ∈ clusterKeptRows M, (clusterRawReferenceLaw PT hPT hm).E
        (fun z => coreRowProduct PT hPT hm i x (M.positions r) z.1 z.2) := by
  classical
  let P (r : ClusterRecordIndex PT hPT hm) : FinLaw (ClusterRecordValue r) :=
    ⟨(clusterSolver PT hPT hm r.1.1).lawRec PT.parameter r.2,
      (clusterSolver PT hPT hm r.1.1).lawRec_nonneg _ _,
      (clusterSolver PT hPT hm r.1.1).lawRec_sum _ _⟩
  let Q := binLawAt PT hPT hm
  let K := wordLabelLaw PT hPT hm
  let F r W B ys := coreRowProduct PT hPT hm i x (M.positions r) W (internalOfWordLabels B ys)
  let SL r := rowCoreWords PT hPT hm (M.positions r)
  let SB r := clusterCoreGroups PT hPT hm (M.positions r)
  let SR r := coreRecordFootprint PT hPT hm (M.positions r)
  have hnotG r (hr : r ∈ clusterKeptRows M) : r ∉ M.geometric :=
    fun hg => (Finset.mem_sdiff.mp hr).2 (Finset.mem_union_left _ hg)
  have hrad6 : (6 : ℝ) ≤ 100 * κ.ρ * (PT.tiling.P i).h := by nlinarith
  have hSB r (hr : r ∈ clusterKeptRows M) t (ht : t ∈ clusterKeptRows M) (hne : r ≠ t) :
      Disjoint (SB r) (SB t) :=
    geometrically_retained_core_groups_disjoint PT hPT hm i M hM hrad6 (hnotG r hr) (hnotG t ht) hne
  have hSL r (hr : r ∈ clusterKeptRows M) t (ht : t ∈ clusterKeptRows M) (hne : r ≠ t) :
      Disjoint (SL r) (SL t) := by
    apply Finset.disjoint_left.mpr
    intro c hc hc'
    apply Finset.disjoint_left.mp (hSB r hr t ht hne)
    · apply row_core_word_groups_subset PT hPT hm (M.positions r)
      exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
    · apply row_core_word_groups_subset PT hPT hm (M.positions t)
      exact Finset.mem_image.mpr ⟨c, hc', rfl⟩
  have hSR r (hr : r ∈ clusterKeptRows M) t (ht : t ∈ clusterKeptRows M) (hne : r ≠ t) :
      Disjoint (SR r) (SR t) :=
    geometrically_retained_core_records_disjoint PT hPT hm i M hM hradius (hnotG r hr) (hnotG t ht) hne
  have hlabel W B r (hr : r ∈ clusterKeptRows M) : FinProb.DependsOn (F r W B) (SL r) :=
    core_row_word_depends PT hPT hm i x (M.positions r) r W B
  have hbin W r (hr : r ∈ clusterKeptRows M) :
      FinProb.DependsOn (fun B => (FinLaw.pi (K W B)).E (F r W B)) (SB r) := by
    intro B B' hBB
    have hE (B : ClusterBinAssignment PT) : (FinLaw.pi (K W B)).E (F r W B) =
        (clusterIndependentLabelKernel PT hPT hm W B).E
          (coreRowProduct PT hPT hm i x (M.positions r) W) :=
      (independent_label_E_eq_word_E PT hPT hm W B _).symm
    dsimp only
    rw [hE, hE]
    exact core_row_bin_depends PT hPT hm i x (M.positions r) r W B B' hBB
  have hhistory r (hr : r ∈ clusterKeptRows M) :
      FinProb.DependsOn (fun W => (FinLaw.pi (Q W)).E
        (fun B => (FinLaw.pi (K W B)).E (F r W B))) (SR r) := by
    intro W W' hWW
    have hE (W : ClusterHistory PT hPT hm) :
        (FinLaw.pi (Q W)).E (fun B => (FinLaw.pi (K W B)).E (F r W B)) =
          (clusterIndependentBinKernel PT hPT hm W).E (fun B =>
            (clusterIndependentLabelKernel PT hPT hm W B).E
              (coreRowProduct PT hPT hm i x (M.positions r) W)) := by
      apply congrArg (FinLaw.E (FinLaw.pi (Q W)))
      funext B
      exact (independent_label_E_eq_word_E PT hPT hm W B _).symm
    dsimp only
    rw [hE, hE]
    exact core_row_history_depends PT hPT hm i x (M.positions r) r W W' hWW
  rw [raw_reference_E_eq_stages]
  simp_rw [raw_reference_E_eq_stages]
  exact E_three_stage_prod P Q K (clusterKeptRows M) F SR SB SL hSL hSB hSR hlabel hbin hhistory

end HypercubeRamsey.Lane_sol_s15_transfer
