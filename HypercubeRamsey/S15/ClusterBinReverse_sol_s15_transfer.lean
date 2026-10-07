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

noncomputable def earlierCrossingGroups {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (M : ClusterMask PT) (q : Fin (T.S.n k) × OddPosition T k) : Finset (ClusterGroupIndex PT) :=
  ((clusterAllowedCrossings PT hPT M).filter fun p => clusterQueryOrder p < clusterQueryOrder q).image
    (fun p => clusterGroupIndexAt PT hPT hm p.2)

theorem crossing_repeat_iff_blocks {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (M : ClusterMask PT) (B : ClusterBinAssignment PT) (q : Fin (T.S.n k) × OddPosition T k) :
    clusterCrossingRepeat PT hPT hm M B q ↔
      ∃ g ∈ ({clusterGroupIndexAt PT hPT hm q.2} : Finset (ClusterGroupIndex PT)),
        ∃ g' ∈ earlierCrossingGroups PT hPT hm M q, (B g).1 = (B g').1 := by
  constructor
  · rintro ⟨p, hp, hpq, hbin⟩
    exact ⟨_, Finset.mem_singleton_self _, _, Finset.mem_image.mpr
      ⟨p, Finset.mem_filter.mpr ⟨hp, hpq⟩, rfl⟩, hbin.symm⟩
  · rintro ⟨g, hg, g', hg', hbin⟩
    have hgq := Finset.mem_singleton.mp hg
    subst g
    obtain ⟨p, hp, hpg⟩ := Finset.mem_image.mp hg'
    have hp' := Finset.mem_filter.mp hp
    rw [← hpg] at hbin
    exact ⟨p, hp'.1, hp'.2, hbin.symm⟩

theorem allowed_crossing_groups_injective {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (M : ClusterMask PT)
    (hwidth : ∀ j, ((PT.tiling.P j).h : ℝ) + 2 ≤ (T.S.n k : ℝ) ^ (2 * κ.ι)) :
    Set.InjOn (fun q : Fin (T.S.n k) × OddPosition T k => clusterGroupIndexAt PT hPT hm q.2)
      (clusterAllowedCrossings PT hPT M) := by
  intro p hp q hq heq
  exact allowed_crossing_slices_injective PT hPT M hwidth hp hq (congrArg Sigma.fst heq)

theorem crossing_reverse_integration {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (M : ClusterMask PT)
    (hmask : M.crossingBins ⊆ clusterAllowedCrossings PT hPT M)
    (hwidth : ∀ j, ((PT.tiling.P j).h : ℝ) + 2 ≤ (T.S.n k : ℝ) ^ (2 * κ.ι))
    (hcap : ∀ j, (T.S.n k : ℝ) ^ 2 * binCap PT j ≤ clusterCrossingFraction T k)
    (W : ClusterHistory PT hPT hm) (F : ClusterBinAssignment PT → ℝ)
    (hF : ∀ B, 0 ≤ F B)
    (hskip : ∀ q ∈ M.crossingBins, ∀ B D,
      F (Function.update B (clusterGroupIndexAt PT hPT hm q.2) D) = F B) :
    (clusterIndependentBinKernel PT hPT hm W).E
      (fun B => if ∀ q ∈ M.crossingBins, clusterCrossingRepeat PT hPT hm M B q then F B else 0) ≤
        clusterCrossingFraction T k ^ M.crossingBins.card *
          (clusterIndependentBinKernel PT hPT hm W).E F := by
  classical
  let queryOrder : LinearOrder (Fin (T.S.n k) × OddPosition T k) :=
    LinearOrder.lift' clusterQueryOrder Lane_q_s15_c2.clusterQueryOrder_injective
  letI := queryOrder
  letI : Preorder (Fin (T.S.n k) × OddPosition T k) := queryOrder.toPreorder
  letI : LT (Fin (T.S.n k) × OddPosition T k) := queryOrder.toLT
  let Q := binLawAt PT hPT hm W
  let C (q : Fin (T.S.n k) × OddPosition T k) : Finset (ClusterGroupIndex PT) :=
    {clusterGroupIndexAt PT hPT hm q.2}
  let D (q : Fin (T.S.n k) × OddPosition T k) := earlierCrossingGroups PT hPT hm M q
  let p (q : Fin (T.S.n k) × OddPosition T k) := binCap PT (clusterGroupIndexAt PT hPT hm q.2).1.1
  have hinj := allowed_crossing_groups_injective PT hPT hm M hwidth
  have hdis q (hq : q ∈ M.crossingBins) : Disjoint (C q) (D q) := by
    apply Finset.disjoint_left.mpr
    intro g hg hg'
    have hgq := Finset.mem_singleton.mp hg
    obtain ⟨u, hu, hug⟩ := Finset.mem_image.mp hg'
    have hu' := Finset.mem_filter.mp hu
    have huq := hinj hu'.1 (hmask hq) (hug.trans hgq)
    subst u
    exact lt_irrefl _ hu'.2
  have hearlier q (hq : q ∈ M.crossingBins) v (hv : v ∈ M.crossingBins) (hqv : q < v) :
      Disjoint (C v) (C q ∪ D q) := by
    apply Finset.disjoint_left.mpr
    intro g hg hg'
    have hgv := Finset.mem_singleton.mp hg
    have hqv' : clusterQueryOrder q < clusterQueryOrder v := hqv
    rcases Finset.mem_union.mp hg' with hgq | hgd
    · have hgq' := Finset.mem_singleton.mp hgq
      have hvq := hinj (hmask hv) (hmask hq) (hgv.symm.trans hgq')
      subst v
      exact lt_irrefl _ hqv'
    · obtain ⟨u, hu, hug⟩ := Finset.mem_image.mp hgd
      have hu' := Finset.mem_filter.mp hu
      have huv := hinj hu'.1 (hmask hv) (hug.trans hgv)
      subst u
      exact lt_asymm hqv' hu'.2
  have hskip' q (hq : q ∈ M.crossingBins) g (hg : g ∈ C q) B A :
      F (Function.update B g A) = F B := by
    have hgq := Finset.mem_singleton.mp hg
    subst g
    exact hskip q hq B A
  have hp q (hq : q ∈ M.crossingBins) : 0 ≤ p q := by dsimp [p, binCap]; positivity
  have hbound := E_pi_charge_repeat_blocks_ordered Q (fun _ B => B.1) M.crossingBins C D p
    F hF hskip' hdis hearlier hp (fun q hq g hg B => by
      have hgq := Finset.mem_singleton.mp hg
      subst g
      exact bin_law_atom_le PT hPT hm W _ B)
  have hbound' : (clusterIndependentBinKernel PT hPT hm W).E
      (fun B => if ∀ q ∈ M.crossingBins, clusterCrossingRepeat PT hPT hm M B q then F B else 0) ≤
      (∏ q ∈ M.crossingBins, (C q).card * (D q).card * p q) * (FinLaw.pi Q).E F := by
    convert hbound using 1
    apply congrArg (FinLaw.E (FinLaw.pi Q))
    funext B
    have heq : (∀ q ∈ M.crossingBins, clusterCrossingRepeat PT hPT hm M B q) ↔
        ∀ q ∈ M.crossingBins, ∃ g ∈ C q, ∃ g' ∈ D q, (B g).1 = (B g').1 := by
      apply forall₂_congr
      intro q hq
      exact crossing_repeat_iff_blocks PT hPT hm M B q
    by_cases h : ∀ q ∈ M.crossingBins, clusterCrossingRepeat PT hPT hm M B q
    · simp only [if_pos h, if_pos (heq.mp h)]
    · simp only [if_neg h, if_neg (fun h' => h (heq.mpr h'))]
  apply hbound'.trans
  apply mul_le_mul_of_nonneg_right _ (E_nonneg _ _ hF)
  calc
    _ ≤ ∏ _q ∈ M.crossingBins, clusterCrossingFraction T k := by
      apply Finset.prod_le_prod₀
      · intro q hq; have h := hp q hq; positivity
      · intro q hq
        have hDnat : (D q).card ≤ (T.S.n k) ^ 2 := by
          apply Finset.card_image_le.trans
          apply (Finset.card_filter_le _ _).trans
          exact allowed_crossings_card_le PT hPT M
        have hD : ((D q).card : ℝ) ≤ (T.S.n k : ℝ) ^ 2 := by exact_mod_cast hDnat
        have hpq := hp q hq
        simp only [C, Finset.card_singleton, Nat.cast_one, one_mul]
        exact (mul_le_mul_of_nonneg_right hD hpq).trans (hcap _)
    _ = _ := by simp

theorem crossing_repeat_skip_core_patch {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (M : ClusterMask PT) (hM : ClusterMaskGeometry PT hPT i M)
    {g : ClusterGroupIndex PT} (hg : g.1.1 = i)
    (B : ClusterBinAssignment PT) (D : clusterBinType g)
    {q : Fin (T.S.n k) × OddPosition T k} (hq : q ∈ clusterAllowedCrossings PT hPT M) :
    clusterCrossingRepeat PT hPT hm M (Function.update B g D) q ↔
      clusterCrossingRepeat PT hPT hm M B q := by
  have hunchanged u (hu : u ∈ clusterAllowedCrossings PT hPT M) :
      (Function.update B g D) (clusterGroupIndexAt PT hPT hm u.2) =
        B (clusterGroupIndexAt PT hPT hm u.2) := by
    apply Function.update_of_ne
    intro heq
    have hp : (clusterGroupIndexAt PT hPT hm u.2).1.1 = i :=
      (congrArg (fun g : ClusterGroupIndex PT => g.1.1) heq).trans hg
    exact allowed_crossing_group_patch_ne PT hPT hm i M hM hu hp
  unfold clusterCrossingRepeat
  apply exists_congr
  intro u
  apply and_congr_right
  intro hu
  apply and_congr_right
  intro horder
  rw [hunchanged u hu, hunchanged q hq]

theorem raw_bin_repeat_bound_small {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (hsmall : PT.tiling.mode = .highSmall)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (M : ClusterMask PT)
    (hM : ClusterMaskGeometry PT hPT i M)
    (hradius : (6 : ℝ) ≤ 100 * κ.ρ * (PT.tiling.P i).h) (hn : 1 ≤ T.S.n k)
    (hwidth : ∀ j, ((PT.tiling.P j).h : ℝ) + 2 ≤ (T.S.n k : ℝ) ^ (2 * κ.ι))
    (hcap : ∀ j, (T.S.n k : ℝ) ^ 2 * binCap PT j ≤ clusterCrossingFraction T k)
    (W : ClusterHistory PT hPT hm) :
    (clusterIndependentBinKernel PT hPT hm W).E
      (fun B => if ClusterMaskConsistent PT hPT hm M B then
        (clusterIndependentLabelKernel PT hPT hm W B).E
          (clusterKeptProduct PT hPT hm i x M W) else 0) ≤
      clusterCoreRepeatCost PT i ^ M.coreBins.card * clusterCrossingFraction T k ^ M.crossingBins.card *
        clusterReferenceMean PT hPT hm i x M W := by
  classical
  let F B := (clusterIndependentLabelKernel PT hPT hm W B).E (clusterKeptProduct PT hPT hm i x M W)
  let A B := ∀ q ∈ M.crossingBins, clusterCrossingRepeat PT hPT hm M B q
  let G B := if A B then F B else 0
  have hF B : 0 ≤ F B := E_nonneg _ _ (kept_product_nonneg PT hPT hm i x M W)
  have hG B : 0 ≤ G B := by dsimp [G]; split_ifs; exact hF B; exact le_rfl
  have hGskip r (hr : r ∈ M.coreBins) g (hg : g ∈ clusterCoreGroups PT hPT hm (M.positions r)) B D :
      G (Function.update B g D) = G B := by
    have hgpatch := (core_group_patch PT hPT hm _ hg).trans
      (Lane_q_s15_c2.patchAt_eq_of_evenPatchPosition hPT (hM.1 r))
    have hA : A (Function.update B g D) ↔ A B := by
      apply forall₂_congr
      intro q hq
      exact crossing_repeat_skip_core_patch PT hPT hm i M hM hgpatch B D (hM.2.2.2 hq)
    have hskip := kept_label_integral_skip_group PT hPT hm i x M W
      (core_bin_removed_groups_not_read PT hPT hm i M hM hradius hr hg) B D
    dsimp only [G]
    by_cases h : A B
    · rw [if_pos h, if_pos (hA.mpr h)]
      exact hskip
    · rw [if_neg h, if_neg (fun h' => h (hA.mp h'))]
  have hcross : (clusterIndependentBinKernel PT hPT hm W).E G ≤
      clusterCrossingFraction T k ^ M.crossingBins.card * (clusterIndependentBinKernel PT hPT hm W).E F := by
    apply crossing_reverse_integration PT hPT hm M hM.2.2.2 hwidth hcap W F hF
    intro q hq B D
    exact kept_label_integral_skip_group PT hPT hm i x M W
      (crossing_bin_removed_group_not_read PT hPT hm i M hM hwidth hq) B D
  calc
    _ ≤ (clusterIndependentBinKernel PT hPT hm W).E
        (fun B => if ∀ r ∈ M.coreBins, clusterCoreRepeat PT hPT hm M B r then G B else 0) := by
      apply E_mono
      intro B
      by_cases h : ClusterMaskConsistent PT hPT hm M B
      · have hcons := h
        rw [ClusterMaskConsistent, if_pos hsmall] at hcons
        have hcore : ∀ r ∈ M.coreBins, clusterCoreRepeat PT hPT hm M B r :=
          fun r hr => ((hcons.1 r).mp hr).2
        have hcross' : A B := fun q hq => ((hcons.2 q).mp hq).2
        simp only [if_pos h, if_pos hcore, G, if_pos hcross']
        exact le_rfl
      · rw [if_neg h]
        split_ifs
        · exact hG B
        · exact le_rfl
    _ ≤ clusterCoreRepeatCost PT i ^ M.coreBins.card * (clusterIndependentBinKernel PT hPT hm W).E G :=
      core_reverse_integration PT hPT hm i M hM hradius hn W G hG hGskip
    _ ≤ clusterCoreRepeatCost PT i ^ M.coreBins.card *
        (clusterCrossingFraction T k ^ M.crossingBins.card * (clusterIndependentBinKernel PT hPT hm W).E F) :=
      mul_le_mul_of_nonneg_left hcross (by unfold clusterCoreRepeatCost; positivity)
    _ = _ := by rw [mul_assoc]; rfl

theorem eventual_high_gain_le_dimension (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ i, PT.tiling.gain i ≤ (T.S.n k : ℝ) := by
  let C : ℝ := κ.a / 10 ^ 6
  have hC : 0 < C := by dsimp [C]; rw [hκ.a_eq]; have hθ := hκ.θ_rng.1; positivity
  have hmin : min κ.xs (min κ.η0 0.01) / 1000 ≤ (0.01 : ℝ) / 1000 :=
    div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)
  have hι : 0 < 1 - κ.ι := by linarith [hκ.ι_rng.2]
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hp := (tendsto_rpow_atTop hι).comp hn
  filter_upwards [hp.eventually (eventually_ge_atTop C),
    T.S.n_tendsto.eventually (eventually_ge_atTop 1)] with k hk hn1
  intro PT hPT hm i
  have hh : ((PT.tiling.P i).h : ℝ) ≤ (T.S.n k : ℝ) ^ κ.ι :=
    (lt_of_le_of_lt (by exact_mod_cast le_max_left (PT.tiling.P i).h (PT.tiling.P i).ℓ)
      (hPT.tiling_valid.allocation_bounds i).1).le
  have hgain : PT.tiling.gain i = C * (PT.tiling.P i).h := by
    rcases hm with hs | hl
    · simp [Tiling.gain, hs, C] <;> ring
    · simp [Tiling.gain, hl, C] <;> ring
  rw [hgain]
  calc
    _ ≤ C * (T.S.n k : ℝ) ^ κ.ι := mul_le_mul_of_nonneg_left hh hC.le
    _ ≤ (T.S.n k : ℝ) ^ (1 - κ.ι) * (T.S.n k : ℝ) ^ κ.ι :=
      mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := by
      have hpos : (0 : ℝ) < (T.S.n k : ℝ) := by exact_mod_cast (by omega : 0 < T.S.n k)
      rw [← Real.rpow_add hpos]
      simp

theorem crossing_bin_cap_of_splice {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hn : 1 ≤ T.S.n k)
    (hgain : ∀ i, PT.tiling.gain i ≤ (T.S.n k : ℝ))
    (hsplice : ∀ i, clusterCoreRepeatCost PT i ≤
      (2 : ℝ) ^ (-(T.S.n k : ℤ)) * Real.exp (0.01 * PT.tiling.gain i)) :
    ∀ i, (T.S.n k : ℝ) ^ 2 * binCap PT i ≤ clusterCrossingFraction T k := by
  intro i
  have hnR : (1 : ℝ) ≤ T.S.n k := by exact_mod_cast hn
  have hcap : 0 ≤ binCap PT i := by dsimp [binCap]; positivity
  calc
    _ ≤ (T.S.n k : ℝ) ^ 4 * binCap PT i :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hnR (by norm_num)) hcap
    _ = clusterCoreRepeatCost PT i := by unfold binCap clusterCoreRepeatCost; ring
    _ ≤ _ := hsplice i
    _ ≤ clusterCrossingFraction T k := by
      unfold clusterCrossingFraction
      gcongr
      exact hgain i

end HypercubeRamsey.Lane_sol_s15_transfer
