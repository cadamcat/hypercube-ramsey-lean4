import HypercubeRamsey.S16.Producers_q_s16_prod1

namespace HypercubeRamsey.S16.WordOrder

open Classical

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}

/-- T16:7–13,167–177 and T17:260–267: the canonical physical slice word retains
the ordered top-coordinate restriction and the outer-parity translation
used by the internal solver (T14:35,95). -/
theorem cluster_cell_words_order {G : LowGeom PT} (C : G.Cell)
    (whole : ∀ v, G.cellOf v = C → ∀ v',
      CellData.sameSlice (G.cellPatch C) v v' → G.cellOf v' = C)
    (hle : (PT.tiling.P (G.cellPatch C)).h ≤ T.S.n k)
    (hpos : 0 < (PT.tiling.P (G.cellPatch C)).h)
    (s : Lane_q_s16_prod1.ClusterCellSlice G C)
    (z : IWord PT.tiling (G.cellPatch C))
    (j : Fin (PT.tiling.P (G.cellPatch C)).h) :
    z j = if ¬ IsEvenRole (fun l : Fin (T.S.n k) =>
      if l ∈ PT.tiling.Icoord (G.cellPatch C) then false else
        (Lane_q_s16_prod1.clusterCellWords C whole hle hpos (s, z)).1 l)
      ∧ j.val = 0
      then !((Lane_q_s16_prod1.clusterCellWords C whole hle hpos (s, z)).1
        (Lane_q_s16_prod1.cellAxis (G.cellPatch C) hle j))
      else (Lane_q_s16_prod1.clusterCellWords C whole hle hpos (s, z)).1
        (Lane_q_s16_prod1.cellAxis (G.cellPatch C) hle j) := by
  let v := (Lane_q_s16_prod1.clusterCellWords C whole hle hpos (s, z)).1
  have houter : (fun l : Fin (T.S.n k) =>
      if l ∈ PT.tiling.Icoord (G.cellPatch C) then false else v l) = s.1 := by
    funext l
    by_cases hl : l ∈ PT.tiling.Icoord (G.cellPatch C)
    · simp only [ite_eq_left hl]
      exact (s.2.2 l hl).symm
    · simp [v, Lane_q_s16_prod1.clusterCellWords,
        Lane_q_s16_prod1.clusterCombine, hl]
  have hjmem : Lane_q_s16_prod1.cellAxis (G.cellPatch C) hle j ∈
      PT.tiling.Icoord (G.cellPatch C) := by
    rw [← Lane_q_s16_prod1.cellAxis_image (G.cellPatch C) hle]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hbit : v (Lane_q_s16_prod1.cellAxis (G.cellPatch C) hle j) =
      Lane_q_s16_prod1.clusterShiftWord s z hpos j := by
    simp [v, Lane_q_s16_prod1.clusterCellWords,
      Lane_q_s16_prod1.clusterCombine, hjmem,
      Lane_q_s16_prod1.cellAxisInv_cellAxis]
  change z j = if ¬ IsEvenRole _ ∧ j.val = 0 then !(v _) else v _
  rw [houter, hbit]
  by_cases hs : IsEvenRole s.1
  · simp [hs, Lane_q_s16_prod1.clusterShiftWord]
  · by_cases hj : j.val = 0
    · have hj' : j = ⟨0, hpos⟩ := Fin.ext hj
      simp [hs, Lane_q_s16_prod1.clusterShiftWord, flipPos, hj']
    · have hj' : j ≠ ⟨0, hpos⟩ := fun h => hj (congrArg Fin.val h)
      simp [hs, hj, Lane_q_s16_prod1.clusterShiftWord, flipPos, hj']

end HypercubeRamsey.S16.WordOrder
