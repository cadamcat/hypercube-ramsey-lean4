import HypercubeRamsey.S16.Comparisons

namespace HypercubeRamsey.S16.Lane_q_s16_prod1

open HypercubeRamsey Classical

abbrev CellSlice {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) (C : G.Cell) :=
  {v : Pos T k // G.cellOf v = C}

abbrev ClusterCellSlice {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) (C : G.Cell) :=
  {v : Pos T k // G.cellOf v = C ∧
    ∀ j, j ∈ PT.tiling.Icoord (G.cellPatch C) → v j = false}

noncomputable def cellAxis {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (i : Fin PT.tiling.m)
    (hh : (PT.tiling.P i).h ≤ T.S.n k) :
    Fin (PT.tiling.P i).h → Fin (T.S.n k) := fun j =>
  ⟨T.S.n k - (PT.tiling.P i).h + j.val, by omega⟩

theorem cellAxis_injective {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (i : Fin PT.tiling.m)
    (hh : (PT.tiling.P i).h ≤ T.S.n k) :
    Function.Injective (cellAxis i hh) := by
  intro a b h
  have hv := congrArg Fin.val h
  dsimp [cellAxis] at hv
  apply Fin.ext
  omega

theorem cellAxis_image {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (i : Fin PT.tiling.m)
    (hh : (PT.tiling.P i).h ≤ T.S.n k) :
    Finset.univ.image (cellAxis i hh) = PT.tiling.Icoord i := by
  classical
  apply Finset.ext
  intro j
  constructor
  · intro hj
    rcases Finset.mem_image.mp hj with ⟨a, _, rfl⟩
    simp [Tiling.Icoord, topCoordinates, cellAxis]
    omega
  · intro hj
    have hj' : (T.S.n k - (PT.tiling.P i).h) ≤ j.val := by
      simpa [Tiling.Icoord, topCoordinates] using hj
    let a : Fin (PT.tiling.P i).h := ⟨j.val - (T.S.n k - (PT.tiling.P i).h), by omega⟩
    refine Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    simp [cellAxis, a]
    omega

noncomputable def cellAxisInv {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (i : Fin PT.tiling.m)
    (hh : (PT.tiling.P i).h ≤ T.S.n k)
    (j : Fin (T.S.n k)) (hj : j ∈ PT.tiling.Icoord i) : Fin (PT.tiling.P i).h :=
  ⟨j.val - (T.S.n k - (PT.tiling.P i).h), by
    have hj' : T.S.n k - (PT.tiling.P i).h ≤ j.val := by
      simpa [Tiling.Icoord, topCoordinates] using hj
    omega⟩

theorem cellAxisInv_axis {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (i : Fin PT.tiling.m)
    (hh : (PT.tiling.P i).h ≤ T.S.n k)
    (j : Fin (T.S.n k)) (hj : j ∈ PT.tiling.Icoord i) :
    cellAxis i hh (cellAxisInv i hh j hj) = j := by
  apply Fin.ext
  have hj' : T.S.n k - (PT.tiling.P i).h ≤ j.val := by
    simpa [Tiling.Icoord, topCoordinates] using hj
  change T.S.n k - (PT.tiling.P i).h +
      (j.val - (T.S.n k - (PT.tiling.P i).h)) = j.val
  exact Nat.add_sub_of_le hj'

theorem cellAxisInv_cellAxis {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (i : Fin PT.tiling.m)
    (hh : (PT.tiling.P i).h ≤ T.S.n k) (a : Fin (PT.tiling.P i).h) :
    cellAxisInv i hh (cellAxis i hh a)
      (by rw [← cellAxis_image i hh]; exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩) = a := by
  apply Fin.ext
  simp [cellAxis, cellAxisInv]

noncomputable def clusterSliceBase {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (C : G.Cell)
    (whole : ∀ v, G.cellOf v = C → ∀ v',
      CellData.sameSlice (G.cellPatch C) v v' → G.cellOf v' = C)
    (v : Pos T k) (hv : G.cellOf v = C) : ClusterCellSlice G C :=
  ⟨fun j => if j ∈ PT.tiling.Icoord (G.cellPatch C) then false else v j,
    whole v hv _ (by
      intro j hj
      simp [hj]), by
    intro j hj
    simp [hj]⟩

noncomputable def clusterShiftWord {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {C : G.Cell}
    (s : ClusterCellSlice G C) (z : IWord PT.tiling (G.cellPatch C))
    (hpos : 0 < (PT.tiling.P (G.cellPatch C)).h) : IWord PT.tiling (G.cellPatch C) :=
  if hs : IsEvenRole s.1 then z else flipPos z ⟨0, hpos⟩

theorem clusterShiftWord_involutive {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {C : G.Cell}
    (s : ClusterCellSlice G C) (z : IWord PT.tiling (G.cellPatch C))
    (hpos : 0 < (PT.tiling.P (G.cellPatch C)).h) :
    clusterShiftWord s (clusterShiftWord s z hpos) hpos = z := by
  by_cases hs : IsEvenRole s.1
  · simp [clusterShiftWord, hs]
  · have hf : flipPos (flipPos z ⟨0, hpos⟩) ⟨0, hpos⟩ = z := by
      funext j
      by_cases hj : j = ⟨0, hpos⟩ <;> simp [flipPos, hj]
    simp [clusterShiftWord, hs, hf]

noncomputable def clusterCombine {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {C : G.Cell}
    (hh : (PT.tiling.P (G.cellPatch C)).h ≤ T.S.n k)
    (s : ClusterCellSlice G C) (z : IWord PT.tiling (G.cellPatch C))
    (hpos : 0 < (PT.tiling.P (G.cellPatch C)).h) : Pos T k := fun j =>
  if hj : j ∈ PT.tiling.Icoord (G.cellPatch C) then
    clusterShiftWord s z hpos (cellAxisInv (G.cellPatch C) hh j hj)
  else s.1 j

noncomputable def clusterRestrict {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {C : G.Cell}
    (hh : (PT.tiling.P (G.cellPatch C)).h ≤ T.S.n k) (v : Pos T k) :
    IWord PT.tiling (G.cellPatch C) := fun a => v (cellAxis (G.cellPatch C) hh a)

noncomputable def clusterCellWords {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (C : G.Cell)
    (whole : ∀ v, G.cellOf v = C → ∀ v',
      CellData.sameSlice (G.cellPatch C) v v' → G.cellOf v' = C)
    (hh : (PT.tiling.P (G.cellPatch C)).h ≤ T.S.n k)
    (hpos : 0 < (PT.tiling.P (G.cellPatch C)).h) :
    (ClusterCellSlice G C × IWord PT.tiling (G.cellPatch C)) ≃ CellSlice G C := by
  let forward : ClusterCellSlice G C × IWord PT.tiling (G.cellPatch C) → CellSlice G C := fun x =>
    ⟨clusterCombine hh x.1 x.2 hpos, by
      apply whole x.1.1 x.1.2.1 _
      intro j hj
      simp [clusterCombine, hj]⟩
  let backward : CellSlice G C → ClusterCellSlice G C × IWord PT.tiling (G.cellPatch C) := fun v =>
    let s := clusterSliceBase C whole v.1 v.2
    (s, clusterShiftWord s (clusterRestrict hh v.1) hpos)
  refine
    { toFun := forward
      invFun := backward
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    rcases x with ⟨s, z⟩
    let u := forward (s, z)
    have hbase : (backward u).1 = s := by
      apply Subtype.ext
      funext j
      by_cases hj : j ∈ PT.tiling.Icoord (G.cellPatch C)
      · simp [u, forward, backward, clusterSliceBase, clusterCombine, hj, s.2.2 j hj]
      · simp [u, forward, backward, clusterSliceBase, clusterCombine, hj]
    have hrestrict : clusterRestrict hh u.1 = clusterShiftWord s z hpos := by
      funext a
      have hmem : cellAxis (G.cellPatch C) hh a ∈ PT.tiling.Icoord (G.cellPatch C) := by
        rw [← cellAxis_image (G.cellPatch C) hh]
        exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
      simp [u, forward, clusterRestrict, clusterCombine, hmem, cellAxisInv_cellAxis]
    apply Prod.ext
    · exact hbase
    · change clusterShiftWord (backward u).1 (clusterRestrict hh u.1) hpos = z
      rw [hbase, hrestrict]
      exact clusterShiftWord_involutive s z hpos
  · intro v
    apply Subtype.ext
    funext j
    by_cases hj : j ∈ PT.tiling.Icoord (G.cellPatch C)
    · have a := cellAxisInv (G.cellPatch C) hh j hj
      have haxis := cellAxisInv_axis (G.cellPatch C) hh j hj
      simp [forward, backward, clusterCombine, clusterRestrict, hj, haxis,
        clusterShiftWord_involutive]
    · simp [forward, backward, clusterSliceBase, clusterCombine, hj]

noncomputable def directCellWords {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) (C : G.Cell)
    (hh : (PT.tiling.P (G.cellPatch C)).h = 0) :
    (CellSlice G C × IWord PT.tiling (G.cellPatch C)) ≃ CellSlice G C := by
  have hsub : Subsingleton (IWord PT.tiling (G.cellPatch C)) := by
    unfold IWord CubePos
    rw [hh]
    infer_instance
  refine
    { toFun := fun x => x.1
      invFun := fun v => (v, default)
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    rcases x with ⟨s, z⟩
    have hz : z = default := hsub.elim _ _
    subst z
    rfl
  · intro v
    rfl

end HypercubeRamsey.S16.Lane_q_s16_prod1
