import HypercubeRamsey.S18.Nodes_sol_s18_n5

namespace HypercubeRamsey.S18.Lane_sol_s18_n5
open Classical Filter
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

private theorem flip_twice (v : Pos T k) (a : Fin (T.S.n k)) : flipPos (flipPos v a) a = v := by
  funext j
  by_cases hj : j = a
  · subst j; simp [flipPos]
  · simp [flipPos, hj]

private theorem flip_distance (v : Pos T k) (a : Fin (T.S.n k)) :
    hammingDist v (flipPos v a) = 1 := by
  have heq : (Finset.univ.filter fun j : Fin (T.S.n k) => v j ≠ flipPos v a j) = {a} := by
    apply Finset.ext
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    by_cases hj : j = a
    · subst j
      cases hv : v a <;> simp [flipPos, hv]
    · have hu : flipPos v a j = v j := Function.update_of_ne hj _ _
      rw [hu]
      simp [hj]
  change (Finset.univ.filter fun j : Fin (T.S.n k) => v j ≠ flipPos v a j).card = 1
  rw [heq, Finset.card_singleton]

private theorem internal_flip_patch (D : LateData hPT) (v : Pos T k) (a : Fin (T.S.n k))
    (ha : a ∈ PT.tiling.Icoord (D.geom.patchOf v)) :
    D.geom.patchOf (flipPos v a) = D.geom.patchOf v := by
  have hlen : (PT.tiling.P (D.geom.patchOf v)).ℓ + (PT.tiling.P (D.geom.patchOf v)).h ≤ T.S.n k :=
    le_trans (Nat.add_le_add
      (Finset.le_sup (f := fun i : Fin PT.tiling.m => (PT.tiling.P i).ℓ) (Finset.mem_univ _))
      (Finset.le_sup (f := fun i : Fin PT.tiling.m => (PT.tiling.P i).h) (Finset.mem_univ _)))
      hPT.tiling_valid.prefix_internal_length
  have htail : T.S.n k - (PT.tiling.P (D.geom.patchOf v)).h ≤ a.val := by
    simpa [Tiling.Icoord, topCoordinates] using ha
  exact HypercubeRamsey.Lane_q_s17_pool.lowGeom_patch_flip_of_after_prefix D.geom hPT v a (by omega)

theorem external_cell_ne_own (D : LateData hPT) (hn : (2 : ℝ) ≤ Real.log (T.S.n k) ^ 3)
    (v : Pos T k) (a : Fin (T.S.n k)) (ha : a ∈ D.externalEarly v) :
    D.geom.cellOf (flipPos v a) ≠ D.geom.cellOf v := by
  intro heq
  have hdiff : v a ≠ flipPos v a a := by cases hv : v a <;> simp [flipPos, hv]
  have hspace := D.l16_valid.cell_spacing v (flipPos v a) heq.symm
    ⟨a, (Finset.mem_filter.mp ha).2.1, hdiff⟩
  rw [flip_distance] at hspace
  norm_num at hspace
  linarith

theorem external_cells_injective (D : LateData hPT) (hn : (2 : ℝ) ≤ Real.log (T.S.n k) ^ 3)
    (v : Pos T k) : Set.InjOn (fun a => D.geom.cellOf (flipPos v a)) (D.externalEarly v : Set _) := by
  intro a ha a' ha' heq
  by_contra hne
  have houtside : a ∉ PT.tiling.Icoord (D.geom.patchOf (flipPos v a)) := by
    intro hinside
    have hp := internal_flip_patch D (flipPos v a) a hinside
    rw [flip_twice] at hp
    have hav : a ∈ PT.tiling.Icoord (D.geom.patchOf v) := by rwa [hp]
    exact (Finset.mem_filter.mp ha).2.1 hav
  have hdiff : flipPos v a a ≠ flipPos v a' a := by
    cases hv : v a <;> simp [flipPos, hne, hv]
  have hspace := D.l16_valid.cell_spacing (flipPos v a) (flipPos v a') heq
    ⟨a, houtside, hdiff⟩
  have hdist : hammingDist (flipPos v a) (flipPos v a') ≤ 2 := by
    have ht := hammingDist_triangle (flipPos v a) v (flipPos v a')
    have hd : hammingDist (flipPos v a) v = 1 := by
      have hs : hammingDist (flipPos v a) v = hammingDist v (flipPos v a) := by
        unfold hammingDist
        congr 1
        ext i
        simp [ne_comm]
      rw [hs]
      exact flip_distance v a
    rw [hd, flip_distance] at ht
    exact ht
  have hdist' : (hammingDist (flipPos v a) (flipPos v a') : ℝ) ≤ 2 := by exact_mod_cast hdist
  linarith

end HypercubeRamsey.S18.Lane_sol_s18_n5
