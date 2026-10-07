import HypercubeRamsey.S16.Producers_q_s16_prod1
import HypercubeRamsey.Tools.CubeGeometry

namespace HypercubeRamsey.S16.Lane_sol_s16_prod1

open Classical
open scoped BigOperators
open Lane_q_s16_prod1

theorem flip_parity {n : ℕ} (z : CubePos n) (j : Fin n) :
    IsEvenRole (flipPos z j) ↔ ¬ IsEvenRole z := by
  have heq : flipPos z j = cubeFlip z j := by
    funext a
    by_cases ha : a = j <;> simp [flipPos, cubeFlip, ha]
  rw [heq]
  exact cubeFlip_parity z j

theorem shift_flip {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {C : G.Cell}
    (s : ClusterCellSlice G C) (z : IWord PT.tiling (G.cellPatch C))
    (hp : 0 < (PT.tiling.P (G.cellPatch C)).h) (a : Fin (PT.tiling.P (G.cellPatch C)).h) :
    clusterShiftWord s (flipPos z a) hp = flipPos (clusterShiftWord s z hp) a := by
  by_cases hs : IsEvenRole s.1
  · simp [clusterShiftWord, hs]
  · simp only [clusterShiftWord, hs, ↓reduceDIte]
    by_cases ha : a = (⟨0, hp⟩ : Fin _)
    · subst a
      rfl
    funext j
    by_cases hj : j = a <;> by_cases hj0 : j = (⟨0, hp⟩ : Fin _) <;>
      simp [flipPos, Function.update_apply, hj, hj0, ha, Ne.symm ha]

theorem combine_flip {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {C : G.Cell}
    (hh : (PT.tiling.P (G.cellPatch C)).h ≤ T.S.n k)
    (s : ClusterCellSlice G C) (z : IWord PT.tiling (G.cellPatch C))
    (hp : 0 < (PT.tiling.P (G.cellPatch C)).h) (a : Fin (PT.tiling.P (G.cellPatch C)).h) :
    clusterCombine hh s (flipPos z a) hp =
      flipPos (clusterCombine hh s z hp) (cellAxis (G.cellPatch C) hh a) := by
  funext j
  by_cases hj : j ∈ PT.tiling.Icoord (G.cellPatch C)
  · have hi : cellAxisInv (G.cellPatch C) hh j hj = a ↔
        j = cellAxis (G.cellPatch C) hh a := by
      constructor
      · intro h
        rw [← cellAxisInv_axis (G.cellPatch C) hh j hj, h]
      · intro h
        apply cellAxis_injective (G.cellPatch C) hh
        rw [cellAxisInv_axis, h]
    have hm : cellAxis (G.cellPatch C) hh a ∈ PT.tiling.Icoord (G.cellPatch C) := by
      rw [← cellAxis_image (G.cellPatch C) hh]
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    simp only [clusterCombine, dif_pos hj]
    rw [shift_flip]
    by_cases hja : j = cellAxis (G.cellPatch C) hh a
    · subst j
      simp [clusterCombine, hm, flipPos, cellAxisInv_cellAxis]
    · have hia := mt hi.mp hja
      simp [clusterCombine, hj, flipPos, hja, hia]
  · have hne : j ≠ cellAxis (G.cellPatch C) hh a := by
      intro h
      apply hj
      rw [h, ← cellAxis_image (G.cellPatch C) hh]
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    simp [clusterCombine, hj, flipPos, hne]

theorem combine_parity {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {C : G.Cell}
    (hh : (PT.tiling.P (G.cellPatch C)).h ≤ T.S.n k)
    (s : ClusterCellSlice G C) (z : IWord PT.tiling (G.cellPatch C))
    (hp : 0 < (PT.tiling.P (G.cellPatch C)).h) :
    IsEvenRole (clusterCombine hh s z hp) ↔ IsEvenRole z := by
  let A := Finset.univ.filter fun j : Fin (T.S.n k) => s.1 j = true
  let B := Finset.univ.filter fun a : Fin (PT.tiling.P (G.cellPatch C)).h =>
    clusterShiftWord s z hp a = true
  have hdis : Disjoint A (B.image (cellAxis (G.cellPatch C) hh)) := by
    apply Finset.disjoint_left.mpr
    intro j hj hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    have hm : cellAxis (G.cellPatch C) hh a ∈ PT.tiling.Icoord (G.cellPatch C) := by
      rw [← cellAxis_image (G.cellPatch C) hh]
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    have := s.2.2 _ hm
    simpa [A, this] using hj
  have hset : (Finset.univ.filter fun j => clusterCombine hh s z hp j = true) =
      A ∪ B.image (cellAxis (G.cellPatch C) hh) := by
    ext j
    by_cases hj : j ∈ PT.tiling.Icoord (G.cellPatch C)
    · have hs := s.2.2 j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.mem_image]
      simp only [clusterCombine, hj, ↓reduceDIte, A, Finset.mem_filter,
        Finset.mem_univ, true_and, hs, Bool.false_eq_true, false_or]
      constructor
      · intro h
        exact ⟨cellAxisInv (G.cellPatch C) hh j hj, by simpa [B] using h,
          cellAxisInv_axis (G.cellPatch C) hh j hj⟩
      · rintro ⟨a, ha, heq⟩
        have hai : a = cellAxisInv (G.cellPatch C) hh j hj := by
          apply cellAxis_injective (G.cellPatch C) hh
          rw [heq, cellAxisInv_axis]
        simpa [B, hai] using ha
    · have hnot : j ∉ B.image (cellAxis (G.cellPatch C) hh) := by
        intro hb
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
        apply hj
        rw [← cellAxis_image (G.cellPatch C) hh]
        exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hnot,
        or_false]
      simp [clusterCombine, hj, A]
  change Even (Finset.univ.filter fun j => clusterCombine hh s z hp j = true).card ↔ _
  rw [hset, Finset.card_union_of_disjoint hdis,
    Finset.card_image_of_injective _ (cellAxis_injective (G.cellPatch C) hh)]
  by_cases hs : IsEvenRole s.1
  · have hA : Even A.card := hs
    have hB : B = Finset.univ.filter fun a => z a = true := by
      simp [B, clusterShiftWord, hs]
    rw [hB]
    rw [Nat.even_add]
    simp only [hA, true_iff]
    rfl
  · have hA : ¬ Even A.card := hs
    have hB : Even B.card ↔ ¬ IsEvenRole z := by
      change IsEvenRole (clusterShiftWord s z hp) ↔ ¬ IsEvenRole z
      rw [clusterShiftWord, dif_neg hs]
      exact flip_parity z ⟨0, hp⟩
    have hadd : Even (A.card + B.card) ↔ (Even A.card ↔ Even B.card) := Nat.even_add
    rw [hadd, hB]
    tauto

theorem map_refl {α : Type*} [Fintype α] [DecidableEq α] (P : FinLaw α) :
    FinLaw.map P (Equiv.refl α).symm = P := by
  cases P
  unfold FinLaw.map
  congr 1
  funext a
  simp [eq_comm]

theorem solver_good_pos {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hv : PT.Valid) (hm : PT.tiling.mode = .lowCluster)
    {i : Fin PT.tiling.m} (S : SliceSolver κ PT.tiling i PT.mesh)
    (hS : PT.solver i = some S) :
    0 < (S.recLaw PT.parameter).pr S.AllGood := by
  have hnonneg : 0 ≤ (S.recLaw PT.parameter).pr S.AllGood := by
    apply Finset.sum_nonneg
    intro W hW
    split_ifs <;> first | exact (S.recLaw PT.parameter).nonneg W | exact le_rfl
  by_contra h
  have hz : (S.recLaw PT.parameter).pr S.AllGood = 0 := le_antisymm (le_of_not_gt h) hnonneg
  have hzero : ∀ y, (PT.π i).w y = 0 := by
    intro y
    rw [hv.low_profile hm i S hS (S.groupOf (fun _ => false)) y]
    simp [SliceSolver.lowOut, hz]
  have := (PT.π i).sum_eq_one
  simp only [hzero, Finset.sum_const_zero] at this
  norm_num at this

theorem solver_qin_sum {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {i : Fin PT.tiling.m}
    (S : SliceSolver κ PT.tiling i PT.mesh) (W : ∀ r, S.Val r)
    (g : HypercubeRamsey.Group PT.tiling i) :
    (∑ D, S.qin W g D) = if (∑ D ∈ S.pretrimBins W g, S.q g W D) = 0 then 0 else 1 := by
  unfold SliceSolver.qin
  by_cases hz : (∑ D ∈ S.pretrimBins W g, S.q g W D) = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte]
    have hdiv : ∀ D, (if D ∈ S.pretrimBins W g then S.q g W D / (∑ D' ∈ S.pretrimBins W g, S.q g W D') else 0) =
      (if D ∈ S.pretrimBins W g then S.q g W D else 0) / (∑ D' ∈ S.pretrimBins W g, S.q g W D')
        := by intro D; split_ifs <;> simp
    simp_rw [hdiv]
    rw [← Finset.sum_div]
    simp [Finset.sum_ite_mem, hz]

theorem solver_pretrim_pos {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hv : PT.Valid) (hm : PT.tiling.mode = .lowCluster)
    {i : Fin PT.tiling.m} (S : SliceSolver κ PT.tiling i PT.mesh)
    (hS : PT.solver i = some S) (W : ∀ r, S.Val r)
    (hW : S.AllGood W) (hpW : (S.recLaw PT.parameter).w W ≠ 0)
    (g : HypercubeRamsey.Group PT.tiling i) :
    0 < ∑ D ∈ S.pretrimBins W g, S.q g W D := by
  let P := S.recLaw PT.parameter
  let mass := fun W' => ∑ D ∈ S.pretrimBins W' g, S.q g W' D
  let f := fun W' => if mass W' = 0 then (0 : ℝ) else 1
  have ha : 0 < P.pr S.AllGood := solver_good_pos hv hm S hS
  have hf : ∀ W', 0 ≤ f W' ∧ f W' ≤ 1 := by
    intro W'
    dsimp [f]
    split_ifs <;> norm_num
  have hnorm : (∑ W', P.w W' * (if S.AllGood W' then f W' else 0)) = P.pr S.AllGood := by
    have hsum := (PT.π i).sum_eq_one
    simp_rw [hv.low_profile hm i S hS g] at hsum
    unfold SliceSolver.lowOut at hsum
    rw [← Finset.sum_div] at hsum
    have heq : (∑ y, ∑ W', P.w W' *
        (if S.AllGood W' then ∑ D, S.qin W' g D * S.U g W' D y else 0)) =
        ∑ W', P.w W' * (if S.AllGood W' then f W' else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro W' hW'
      rw [← Finset.mul_sum]
      congr 1
      by_cases hg : S.AllGood W'
      · simp only [hg, ↓reduceIte]
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum, S.U_sum, mul_one]
        exact solver_qin_sum S W' g
      · simp [hg]
    change (∑ y, ∑ W', P.w W' *
      (if S.AllGood W' then ∑ D, S.qin W' g D * S.U g W' D y else 0)) /
        P.pr S.AllGood = 1 at hsum
    rw [heq] at hsum
    exact (div_eq_one_iff_eq (ne_of_gt ha)).mp hsum
  have hdef : (∑ W', ((if S.AllGood W' then P.w W' else 0) -
      P.w W' * (if S.AllGood W' then f W' else 0))) = 0 := by
    rw [Finset.sum_sub_distrib, hnorm]
    simp [FinLaw.pr]
  have hn : ∀ W', 0 ≤ (if S.AllGood W' then P.w W' else 0) -
      P.w W' * (if S.AllGood W' then f W' else 0) := by
    intro W'
    by_cases hg : S.AllGood W'
    · simp only [hg, ↓reduceIte]
      nlinarith [P.nonneg W', (hf W').2]
    · simp [hg]
  have hterm := Finset.single_le_sum (fun W' _ => hn W') (Finset.mem_univ W)
  rw [hdef] at hterm
  have hnonneg : 0 ≤ mass W := Finset.sum_nonneg fun D _ => S.q_nonneg g W D
  by_contra h
  have hz : mass W = 0 := le_antisymm (le_of_not_gt h) hnonneg
  have hpos : 0 < P.w W := lt_of_le_of_ne (P.nonneg W) (Ne.symm hpW)
  simp [hW, f, hz] at hterm
  linarith

end HypercubeRamsey.S16.Lane_sol_s16_prod1
