import HypercubeRamsey.S15.ClusterSeparation_sol_s15_transfer
import HypercubeRamsey.S15.ClusterReverse_sol_s15_transfer

namespace HypercubeRamsey.Lane_sol_s15_transfer

open Classical S15 Filter
open scoped BigOperators

noncomputable def binCap {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (i : Fin PT.tiling.m) : ℝ :=
  4 * Real.exp (2 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i) *
    (PT.tiling.P i).d / (PT.tiling.P i).M

noncomputable def binLawAt {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (g : ClusterGroupIndex PT) : FinLaw (clusterBinType g) :=
  ⟨(clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1),
    (clusterSolver PT hPT hm g.1.1).q_nonneg _ _, (clusterSolver PT hPT hm g.1.1).q_sum _ _⟩

theorem bin_law_atom_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (g : ClusterGroupIndex PT)
    (D : Finset (Fin (T.S.N k))) :
    (binLawAt PT hPT hm W g).pr (fun B => B.1 = D) ≤ binCap PT g.1.1 := by
  apply pr_injective_value_le_cap _ Subtype.val Subtype.val_injective
  · dsimp [binCap]; positivity
  · exact (clusterSolver PT hPT hm g.1.1).q_cap _ _

noncomputable def earlierCoreGroups {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (M : ClusterMask PT) (r : Fin (T.S.n k)) : Finset (ClusterGroupIndex PT) :=
  (Finset.univ.filter fun t => t < r ∧ t ∉ M.geometric).biUnion
    (fun t => clusterCoreGroups PT hPT hm (M.positions t))

theorem core_repeat_iff_blocks {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (M : ClusterMask PT) (B : ClusterBinAssignment PT) (r : Fin (T.S.n k)) :
    clusterCoreRepeat PT hPT hm M B r ↔
      ∃ g ∈ clusterCoreGroups PT hPT hm (M.positions r),
        ∃ g' ∈ earlierCoreGroups PT hPT hm M r, (B g).1 = (B g').1 := by
  constructor
  · rintro ⟨t, htr, ht, g, hg, g', hg', hbin⟩
    exact ⟨g, hg, g', Finset.mem_biUnion.mpr
      ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, htr, ht⟩, hg'⟩, hbin⟩
  · rintro ⟨g, hg, g', hg', hbin⟩
    obtain ⟨t, ht, hgt⟩ := Finset.mem_biUnion.mp hg'
    have ht' := (Finset.mem_filter.mp ht).2
    exact ⟨t, ht'.1, ht'.2, g, hg, g', hgt, hbin⟩

theorem core_vs_earlier_disjoint {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (M : ClusterMask PT) (hM : ClusterMaskGeometry PT hPT i M)
    (hradius : (6 : ℝ) ≤ 100 * κ.ρ * (PT.tiling.P i).h)
    {r : Fin (T.S.n k)} (hr : r ∉ M.geometric) :
    Disjoint (clusterCoreGroups PT hPT hm (M.positions r)) (earlierCoreGroups PT hPT hm M r) := by
  apply Finset.disjoint_left.mpr
  intro g hg hg'
  obtain ⟨t, ht, hgt⟩ := Finset.mem_biUnion.mp hg'
  have ht' := (Finset.mem_filter.mp ht).2
  exact Finset.disjoint_left.mp
    (geometrically_retained_core_groups_disjoint PT hPT hm i M hM hradius hr ht'.2
      (ne_of_gt ht'.1)) hg hgt

theorem later_core_vs_earlier_block_disjoint {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (M : ClusterMask PT) (hM : ClusterMaskGeometry PT hPT i M)
    (hradius : (6 : ℝ) ≤ 100 * κ.ρ * (PT.tiling.P i).h)
    {r t : Fin (T.S.n k)} (hr : r ∉ M.geometric) (ht : t ∉ M.geometric) (hrt : r < t) :
    Disjoint (clusterCoreGroups PT hPT hm (M.positions t))
      (clusterCoreGroups PT hPT hm (M.positions r) ∪ earlierCoreGroups PT hPT hm M r) := by
  apply Finset.disjoint_union_right.mpr
  refine ⟨geometrically_retained_core_groups_disjoint PT hPT hm i M hM hradius ht hr
    (ne_of_gt hrt), ?_⟩
  apply Finset.disjoint_left.mpr
  intro g hg hg'
  obtain ⟨u, hu, hgu⟩ := Finset.mem_biUnion.mp hg'
  have hu' := (Finset.mem_filter.mp hu).2
  exact Finset.disjoint_left.mp
    (geometrically_retained_core_groups_disjoint PT hPT hm i M hM hradius ht hu'.2
      (ne_of_gt (hu'.1.trans hrt))) hg hgu

theorem earlier_core_groups_card_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (M : ClusterMask PT) (r : Fin (T.S.n k)) :
    (earlierCoreGroups PT hPT hm M r).card ≤ (T.S.n k) ^ 2 := by
  unfold earlierCoreGroups
  calc
    _ ≤ ∑ t ∈ Finset.univ.filter (fun t => t < r ∧ t ∉ M.geometric),
      (clusterCoreGroups PT hPT hm (M.positions t)).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ Finset.univ.filter (fun t => t < r ∧ t ∉ M.geometric), T.S.n k :=
      Finset.sum_le_sum fun t ht => core_groups_card_le PT hPT hm _
    _ ≤ (T.S.n k) * T.S.n k := by
      simp only [Finset.sum_const, smul_eq_mul]
      apply Nat.mul_le_mul_right
      exact (Finset.card_filter_le _ _).trans_eq (by simp)
    _ = _ := by ring

theorem core_reverse_integration {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (M : ClusterMask PT) (hM : ClusterMaskGeometry PT hPT i M)
    (hradius : (6 : ℝ) ≤ 100 * κ.ρ * (PT.tiling.P i).h) (hn : 1 ≤ T.S.n k)
    (W : ClusterHistory PT hPT hm) (F : ClusterBinAssignment PT → ℝ)
    (hF : ∀ B, 0 ≤ F B)
    (hskip : ∀ r ∈ M.coreBins, ∀ g ∈ clusterCoreGroups PT hPT hm (M.positions r),
      ∀ B D, F (Function.update B g D) = F B) :
    (clusterIndependentBinKernel PT hPT hm W).E
      (fun B => if ∀ r ∈ M.coreBins, clusterCoreRepeat PT hPT hm M B r then F B else 0) ≤
        clusterCoreRepeatCost PT i ^ M.coreBins.card *
          (clusterIndependentBinKernel PT hPT hm W).E F := by
  classical
  let Q := binLawAt PT hPT hm W
  let C r := clusterCoreGroups PT hPT hm (M.positions r)
  let D r := earlierCoreGroups PT hPT hm M r
  have hnR : (1 : ℝ) ≤ T.S.n k := by exact_mod_cast hn
  have hrg r (hr : r ∈ M.coreBins) : r ∉ M.geometric :=
    fun h => Finset.disjoint_left.mp hM.2.2.1 h hr
  have hcap : 0 ≤ binCap PT i := by dsimp [binCap]; positivity
  have hbound := E_pi_charge_repeat_blocks_ordered Q (fun _ B => B.1) M.coreBins C D
    (fun _ => binCap PT i) F hF hskip
    (fun r hr => core_vs_earlier_disjoint PT hPT hm i M hM hradius (hrg r hr))
    (fun r hr t ht hrt => later_core_vs_earlier_block_disjoint PT hPT hm i M hM hradius
      (hrg r hr) (hrg t ht) hrt) (fun _ _ => hcap)
    (fun r hr g hg B => by
      have hp := (core_group_patch PT hPT hm _ hg).trans
        (Lane_q_s15_c2.patchAt_eq_of_evenPatchPosition hPT (hM.1 r))
      simpa only [hp] using bin_law_atom_le PT hPT hm W g B)
  have hfun : (fun B : ClusterBinAssignment PT => if ∀ r ∈ M.coreBins,
      clusterCoreRepeat PT hPT hm M B r then F B else 0) =
      (fun B => if ∀ r ∈ M.coreBins, ∃ g ∈ C r, ∃ g' ∈ D r, (B g).1 = (B g').1 then F B else 0) := by
    funext B
    have heq : (∀ r ∈ M.coreBins, clusterCoreRepeat PT hPT hm M B r) ↔
        ∀ r ∈ M.coreBins, ∃ g ∈ C r, ∃ g' ∈ D r, (B g).1 = (B g').1 := by
      apply forall₂_congr
      intro r hr
      exact core_repeat_iff_blocks PT hPT hm M B r
    simp only [heq]
  rw [hfun]
  change (FinLaw.pi Q).E _ ≤ clusterCoreRepeatCost PT i ^ M.coreBins.card * (FinLaw.pi Q).E F
  have hbound' : (FinLaw.pi Q).E (fun B => if ∀ r ∈ M.coreBins,
      ∃ g ∈ C r, ∃ g' ∈ D r, (B g).1 = (B g').1 then F B else 0) ≤
      (∏ r ∈ M.coreBins, (C r).card * (D r).card * binCap PT i) * (FinLaw.pi Q).E F := by
    convert hbound using 1
    apply congrArg (FinLaw.E (FinLaw.pi Q))
    funext B
    by_cases h : ∀ r ∈ M.coreBins, ∃ g ∈ C r, ∃ g' ∈ D r, (B g).1 = (B g').1
    · simp only [if_pos h]
    · simp only [if_neg h]
  apply hbound'.trans
  apply mul_le_mul_of_nonneg_right _ (E_nonneg _ _ hF)
  calc
    _ ≤ ∏ _r ∈ M.coreBins, clusterCoreRepeatCost PT i := by
      apply Finset.prod_le_prod₀
      · intro r hr; positivity
      · intro r hr
        have hC : ((C r).card : ℝ) ≤ (T.S.n k : ℝ) := by
          exact_mod_cast core_groups_card_le PT hPT hm (M.positions r)
        have hD : ((D r).card : ℝ) ≤ (T.S.n k : ℝ) ^ 2 := by
          exact_mod_cast earlier_core_groups_card_le PT hPT hm M r
        have hn34 : (T.S.n k : ℝ) ^ 3 ≤ (T.S.n k : ℝ) ^ 4 := by
          have h := mul_le_mul_of_nonneg_left hnR (pow_nonneg (Nat.cast_nonneg (T.S.n k)) 3)
          simpa only [mul_one, ← pow_succ] using h
        calc
          _ ≤ ((T.S.n k : ℝ) * (T.S.n k : ℝ) ^ 2) * binCap PT i := by gcongr
          _ = (T.S.n k : ℝ) ^ 3 * binCap PT i := by ring
          _ ≤ (T.S.n k : ℝ) ^ 4 * binCap PT i := mul_le_mul_of_nonneg_right hn34 hcap
          _ = clusterCoreRepeatCost PT i := by unfold binCap clusterCoreRepeatCost; ring
    _ = _ := by simp

end HypercubeRamsey.Lane_sol_s15_transfer
