import HypercubeRamsey.S15.ClusterNodes_q_s15_c2
import HypercubeRamsey.S15.ClusterNodes_sol_s15_load
import HypercubeRamsey.S15.ClusterNodes_sol_s15_transfer

namespace HypercubeRamsey.Lane_sol_s15_c2

open HypercubeRamsey.S15 OAI.HypercubeRamsey Classical Filter
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem law_ext {Ω : Type*} [Fintype Ω] (P Q : FinLaw Ω) (h : P.w = Q.w) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

noncomputable def restrictLaw {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (A : Ω → Prop)
    (hA : ∀ ω, ¬ A ω → P.w ω = 0) : FinLaw {ω // A ω} where
  w ω := P.w ω.1
  nonneg ω := P.nonneg ω.1
  sum_one := by
    classical
    rw [← Finset.sum_subtype (Finset.univ.filter A) (by intro ω; simp) P.w]
    rw [Finset.sum_filter]
    have hterm (ω : Ω) : (if A ω then P.w ω else 0) = P.w ω := by
      by_cases h : A ω
      · simp [h]
      · simp [h, hA ω h]
    simp_rw [hterm]
    exact P.sum_one

theorem restrictLaw_E {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (A : Ω → Prop)
    (hA : ∀ ω, ¬ A ω → P.w ω = 0) (F : Ω → ℝ) :
    (restrictLaw P A hA).E (fun ω => F ω.1) = P.E F := by
  classical
  unfold FinLaw.E
  change (∑ ω : {ω // A ω}, P.w ω.1 * F ω.1) = ∑ ω, P.w ω * F ω
  rw [← Finset.sum_subtype (Finset.univ.filter A) (by intro ω; simp) (fun ω => P.w ω * F ω)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases h : A ω <;> simp [h, hA ω]

theorem restrictLaw_map_val {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FinLaw Ω) (A : Ω → Prop) (hA : ∀ ω, ¬ A ω → P.w ω = 0) :
    FinLaw.map (restrictLaw P A hA) Subtype.val = P := by
  classical
  apply law_ext
  funext ω
  change (∑ v : {ω // A ω}, if v.1 = ω then P.w v.1 else 0) = P.w ω
  rw [← Finset.sum_subtype (Finset.univ.filter A) (by intro ω; simp)
    (fun v => if v = ω then P.w v else 0)]
  rw [Finset.sum_filter]
  have hterm (v : Ω) : (if A v then (if v = ω then P.w v else 0) else 0) =
      if v = ω then (if A ω then P.w ω else 0) else 0 := by
    by_cases h : v = ω
    · subst v; simp
    · simp [h]
  simp_rw [hterm]
  by_cases h : A ω
  · simp [h]
  · simp [h, hA ω h]

theorem row_weight_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (I : ClusterInternalData PT)
    (a : EvenPosition T k) (x : Fin (T.S.N k)) :
    0 ≤ clusterRowWeight PT hPT hm W I a x := by
  unfold clusterRowWeight
  apply mul_nonneg
  · exact mul_nonneg (Lane_sol_s15_load.clusterSigma_nonneg PT hPT hm W I a x)
      (by split_ifs <;> norm_num)
  · apply Finset.prod_nonneg
    intro b hb
    dsimp [clusterFactor]
    split_ifs with hd
    · exact div_nonneg (by unfold hit; split_ifs <;> norm_num) hd.le
    · exact le_rfl

theorem row_weight_sigma_ne_zero {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (I : ClusterInternalData PT)
    (a : EvenPosition T k) (x : Fin (T.S.N k))
    (hx : clusterRowWeight PT hPT hm W I a x ≠ 0) :
    clusterSigma PT hPT hm W I a x ≠ 0 := by
  intro hz
  apply hx
  simp [clusterRowWeight, hz]

theorem row_weight_common_neighbour {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (hn : 0 < T.S.n k) (W : ClusterHistory PT hPT hm) (I : ClusterInternalData PT)
    (a : EvenPosition T k) (x : Fin (T.S.N k))
    (hx : clusterRowWeight PT hPT hm W I a x ≠ 0)
    (b : OddPosition T k) (hab : Adjacent a b) :
    Hits (T.S.E k) PT.tiling.c x (clusterLabelFromInternal (hPT := hPT) hm I b) := by
  by_cases hext : b ∈ clusterBulkNeighbours PT hPT a ∪ clusterCrossingNeighbours PT hPT a
  · have hprod : (∏ c ∈ clusterBulkNeighbours PT hPT a ∪ clusterCrossingNeighbours PT hPT a,
        clusterFactor PT hPT hm W I a c x) ≠ 0 := by
      intro hz
      apply hx
      simp [clusterRowWeight, hz]
    have hf := Finset.prod_ne_zero_iff.mp hprod b hext
    dsimp [clusterFactor] at hf
    split_ifs at hf with hd
    · by_contra hh
      have hhit : hit (T.S.E k) PT.tiling.c x (clusterLabelFromInternal (hPT := hPT) hm I b) = 0 := by
        simp [hit, hh]
      exact hf (by simpa [clusterLabelFromInternal] using congrArg (fun z : ℝ => z / clusterDegree PT hPT hm W b x) hhit)
    · exact (hf rfl).elim
  · have hp : patchAt PT hPT b.1 = patchAt PT hPT a.1 := by
      by_contra hne
      exact hext (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hne⟩))
    have hs : clusterSliceAt PT hPT b.1 = clusterSliceAt PT hPT a.1 := by
      by_contra hne
      exact hext (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hp, hne⟩))
    obtain ⟨l, hl⟩ := Lane_q_s15_c2.clusterSameSlice_internal_neighbor PT hPT hn a b hab hs
    have hσx := row_weight_sigma_ne_zero PT hPT hm W I a x hx
    have hσ : (clusterSolver PT hPT hm (patchAt PT hPT a.1)).σ
        (clusterCenterRole PT hPT hm a) (historyOnSlice W (clusterSliceAt PT hPT a.1))
        (nbrLabels (clusterCenterRole PT hPT hm a).1 (I (clusterSliceAt PT hPT a.1)).2) ≠ 0 := by
      intro hz
      exact hσx (congrFun hz x)
    obtain ⟨v, hv, hsupp⟩ := (clusterSolver PT hPT hm (patchAt PT hPT a.1)).σ_support
      (clusterCenterRole PT hPT hm a) (historyOnSlice W (clusterSliceAt PT hPT a.1))
      (nbrLabels (clusterCenterRole PT hPT hm a).1 (I (clusterSliceAt PT hPT a.1)).2) hσ
    have hhit := (hsupp x hσx).2 l
    have hlabel : clusterLabelFromInternal (hPT := hPT) hm I b =
        (I (clusterSliceAt PT hPT a.1)).2 (flipPos (clusterCenterRole PT hPT hm a).1 l) := by
      convert Lane_q_s15_c2.clusterLabelFromInternal_internalNeighbor I a l using 1
      congr 1
      apply Subtype.ext
      exact hl
    rw [hlabel]
    exact hhit

end HypercubeRamsey.Lane_sol_s15_c2
