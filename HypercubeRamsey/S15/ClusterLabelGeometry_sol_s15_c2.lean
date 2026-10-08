import HypercubeRamsey.S15.ClusterSeparation_sol_s15_transfer

namespace HypercubeRamsey.Lane_sol_s15_c2

open HypercubeRamsey.S15 OAI.HypercubeRamsey Classical
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem flip_involutive {n : ℕ} (v : CubeVertex n) (j : Fin n) :
    flipPos (flipPos v j) j = v := by
  funext t
  by_cases ht : t = j <;> simp [flipPos, ht]

theorem wordAtOdd_injective {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) :
    Function.Injective (Lane_sol_s15_transfer.wordAtOdd PT hPT hm) := by
  intro b c hbc
  have hparts := Sigma.mk.inj_iff.mp hbc
  let i := patchAt PT hPT b.1
  have hpB : patchAt PT hPT b.1 = i := rfl
  have hpC : patchAt PT hPT c.1 = i := (congrArg Sigma.fst hparts.1).symm
  let e0 : Fin (PT.tiling.P i).h := ⟨0, clusterHeight_pos PT hPT hm i⟩
  have hfixed : Lane_sol_s15_transfer.solverWordFixed PT hPT hm i b.1 =
      Lane_sol_s15_transfer.solverWordFixed PT hPT hm i c.1 := by
    apply eq_of_heq
    exact (Lane_sol_s15_transfer.solver_word_fixed_heq PT hPT hm i b.1 hpB).symm.trans
      (hparts.2.trans (Lane_sol_s15_transfer.solver_word_fixed_heq PT hPT hm i c.1 hpC))
  have hraw : internalWord PT hPT i b.1 = internalWord PT hPT i c.1 ∨
      flipPos (internalWord PT hPT i b.1) e0 = internalWord PT hPT i c.1 := by
    unfold Lane_sol_s15_transfer.solverWordFixed at hfixed
    dsimp only at hfixed
    change (if HypercubeRamsey.IsEvenRole (internalWord PT hPT i b.1) ↔ HypercubeRamsey.IsEvenRole b.1 then
      internalWord PT hPT i b.1 else flipPos (internalWord PT hPT i b.1) e0) =
      (if HypercubeRamsey.IsEvenRole (internalWord PT hPT i c.1) ↔ HypercubeRamsey.IsEvenRole c.1 then
        internalWord PT hPT i c.1 else flipPos (internalWord PT hPT i c.1) e0) at hfixed
    by_cases hB : HypercubeRamsey.IsEvenRole (internalWord PT hPT i b.1) ↔ HypercubeRamsey.IsEvenRole b.1 <;>
      by_cases hC : HypercubeRamsey.IsEvenRole (internalWord PT hPT i c.1) ↔ HypercubeRamsey.IsEvenRole c.1
    · exact Or.inl (by simpa only [if_pos hB, if_pos hC] using hfixed)
    · right
      have h := congrArg (fun z => flipPos z e0) hfixed
      simpa only [if_pos hB, if_neg hC, flip_involutive] using h
    · exact Or.inr (by simpa only [if_neg hB, if_pos hC] using hfixed)
    · left
      have h := congrArg (fun z => flipPos z e0) hfixed
      simpa only [if_neg hB, if_neg hC, flip_involutive] using h
  rcases hraw with hraw | hraw
  · apply Subtype.ext
    apply Lane_q_s15_c2.position_eq_of_same_slice_and_internal hPT hparts.1
    change HEq (internalWord PT hPT (patchAt PT hPT b.1) b.1)
      (internalWord PT hPT (patchAt PT hPT c.1) c.1)
    rw [hpB, hpC]
    exact heq_of_eq hraw
  · let j : Fin (T.S.n k) := ⟨T.S.n k - (PT.tiling.P i).h + e0.val,
      by have := clusterHeight_le PT hPT i; have := e0.isLt; omega⟩
    have hflipSlice : clusterSliceAt PT hPT (flipPos b.1 j) = clusterSliceAt PT hPT b.1 :=
      Lane_q_s15_c2.clusterSliceAt_flip_internal PT hPT b.1 e0
    have hflipPatch : patchAt PT hPT (flipPos b.1 j) = i :=
      Lane_q_s15_c2.patchAt_flip_internal PT hPT b.1 e0
    have hflipEq : flipPos b.1 j = c.1 := by
      apply Lane_q_s15_c2.position_eq_of_same_slice_and_internal hPT (hflipSlice.trans hparts.1)
      change HEq (internalWord PT hPT (patchAt PT hPT (flipPos b.1 j)) (flipPos b.1 j))
        (internalWord PT hPT (patchAt PT hPT c.1) c.1)
      rw [hflipPatch, hpC]
      apply heq_of_eq
      exact (Lane_q_s15_c2.internalWord_flip_top PT hPT i b.1 e0).trans hraw
    have hEven : HypercubeRamsey.IsEvenRole (flipPos b.1 j) := (evenRole_flipPos b.1 j).mpr b.2
    exact (c.2 (hflipEq ▸ hEven)).elim

theorem group_role_count_le_height {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) (g : ClusterGroupIndex PT) :
    (Finset.univ.filter fun b : OddPosition T k => clusterGroupIndexAt PT hPT hm b = g).card ≤
      (PT.tiling.P g.1.1).h := by
  let A := Finset.univ.filter fun b : OddPosition T k => clusterGroupIndexAt PT hPT hm b = g
  let choices : Finset (ClusterConsultation PT) := (groupFiber g.2).image fun z => ⟨g.1, z⟩
  have hsub : A.image (Lane_sol_s15_transfer.wordAtOdd PT hPT hm) ⊆ choices := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
    have hodd : ¬ HypercubeRamsey.IsEvenRole (solverWordAt PT hPT hm b.1) := by
      have h := Lane_sol_s15_transfer.solver_word_odd_fixed PT hPT hm (patchAt PT hPT b.1) b
      simpa [Lane_sol_s15_transfer.solverWordFixed, solverWordAt, clusterWordAt] using h
    have hmem := (clusterSolver PT hPT hm (patchAt PT hPT b.1)).groupOf_spec (solverWordAt PT hPT hm b.1) hodd
    have hchoice : Lane_sol_s15_transfer.wordAtOdd PT hPT hm b ∈
        (groupFiber (clusterGroupIndexAt PT hPT hm b).2).image
          (fun z => (⟨(clusterGroupIndexAt PT hPT hm b).1, z⟩ : ClusterConsultation PT)) :=
      Finset.mem_image.mpr ⟨solverWordAt PT hPT hm b.1, hmem, rfl⟩
    rw [(Finset.mem_filter.mp hb).2] at hchoice
    exact hchoice
  calc
    A.card = (A.image (Lane_sol_s15_transfer.wordAtOdd PT hPT hm)).card :=
      (Finset.card_image_of_injective _ (wordAtOdd_injective PT hPT hm)).symm
    _ ≤ choices.card := Finset.card_le_card hsub
    _ ≤ (groupFiber g.2).card := Finset.card_image_le
    _ ≤ (PT.tiling.P g.1.1).h := by
      unfold groupFiber
      exact Finset.card_image_le.trans_eq (by simp)

noncomputable def groupLabelLaw {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT) (g : ClusterGroupIndex PT) :
    FinLaw (Fin (T.S.N k)) :=
  ⟨(clusterSolver PT hPT hm g.1.1).U g.2 (historyOnSlice W g.1) (B g),
    (clusterSolver PT hPT hm g.1.1).U_nonneg g.2 (historyOnSlice W g.1) (B g),
    (clusterSolver PT hPT hm g.1.1).U_sum g.2 (historyOnSlice W g.1) (B g)⟩

noncomputable def oddLabelLaw {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT) (b : OddPosition T k) :
    FinLaw (Fin (T.S.N k)) := groupLabelLaw PT hPT hm W B (clusterGroupIndexAt PT hPT hm b)

theorem odd_label_column_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT) (y : Fin (T.S.N k)) :
    (∑ b : OddPosition T k, (oddLabelLaw PT hPT hm W B b).w y) ≤ clusterGivenBinColumn PT hPT hm W B y := by
  let U := fun g => (groupLabelLaw PT hPT hm W B g).w y
  have heq : (∑ b : OddPosition T k, U (clusterGroupIndexAt PT hPT hm b)) =
      ∑ g : ClusterGroupIndex PT,
        ((Finset.univ.filter fun b : OddPosition T k => clusterGroupIndexAt PT hPT hm b = g).card : ℝ) * U g := by
    calc
      _ = ∑ b : OddPosition T k, ∑ g : ClusterGroupIndex PT,
          if clusterGroupIndexAt PT hPT hm b = g then U g else 0 := by simp
      _ = ∑ g : ClusterGroupIndex PT, ∑ b : OddPosition T k,
          if clusterGroupIndexAt PT hPT hm b = g then U g else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro g hg
        rw [← Finset.sum_filter]
        simp
  change (∑ b : OddPosition T k, U (clusterGroupIndexAt PT hPT hm b)) ≤ _
  rw [heq]
  change (∑ g : ClusterGroupIndex PT, _ * U g) ≤ ∑ g : ClusterGroupIndex PT, (PT.tiling.P g.1.1).h * U g
  apply Finset.sum_le_sum
  intro g hg
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast group_role_count_le_height PT hPT hm g
  · exact (groupLabelLaw PT hPT hm W B g).nonneg y

theorem row_weight_label_depends {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k) (x : Fin (T.S.N k)) :
    ClusterLabelDependsOn hPT hm (fun I => clusterRowWeight PT hPT hm W I a x)
      (Lane_q_s15_direct.star a) := by
  intro I I' hI
  have hσ : clusterSigma PT hPT hm W I a x = clusterSigma PT hPT hm W I' a x := by
    unfold clusterSigma
    apply congrArg (fun labs => (clusterSolver PT hPT hm (patchAt PT hPT a.1)).σ
      (clusterCenterRole PT hPT hm a) (historyOnSlice W (clusterSliceAt PT hPT a.1)) labs x)
    funext l
    let b := Lane_sol_s15_transfer.internalOddNeighbour PT hPT a l
    have hab : Adjacent a b := by
      change _root_.hammingDist a.1 b.1 = 1
      rw [Lane_sol_s15_transfer.hd_comm]
      exact Lane_sol_s15_transfer.flip_dist_one a.1 _
    have hb : b ∈ Lane_q_s15_direct.star a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩
    have h := hI b hb
    have hleft := Lane_q_s15_c2.clusterLabelFromInternal_internalNeighbor (hPT := hPT) (hm := hm) I a l
    have hright := Lane_q_s15_c2.clusterLabelFromInternal_internalNeighbor (hPT := hPT) (hm := hm) I' a l
    exact hleft.symm.trans (h.trans hright)
  unfold clusterRowWeight
  dsimp only
  rw [hσ]
  congr 1
  apply Finset.prod_congr rfl
  intro b hb
  have hab : Adjacent a b := by
    rcases Finset.mem_union.mp hb with hb | hb <;> exact (Finset.mem_filter.mp hb).2.1
  have heq := hI b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩)
  unfold clusterFactor
  change (if 0 < clusterDegree PT hPT hm W b x then
    hit (T.S.E k) PT.tiling.c x (clusterLabelFromInternal (hPT := hPT) hm I b) / clusterDegree PT hPT hm W b x else 0) = _
  rw [heq]
  rfl

theorem row_mass_label_depends {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k) :
    ClusterLabelDependsOn hPT hm (fun I => clusterRowMass PT hPT hm W I a)
      (Lane_q_s15_direct.star a) := by
  intro I I' hI
  unfold clusterRowMass
  apply Finset.sum_congr rfl
  intro x hx
  exact row_weight_label_depends PT hPT hm W a x I I' hI

end HypercubeRamsey.Lane_sol_s15_c2
