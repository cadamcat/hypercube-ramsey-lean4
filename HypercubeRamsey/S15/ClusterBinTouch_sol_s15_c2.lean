import HypercubeRamsey.S15.ClusterBinProb_sol_s15_c2
import HypercubeRamsey.S15.ClusterCapacityScales_sol_s15_c2

namespace HypercubeRamsey.Lane_sol_s15_c2

open HypercubeRamsey.S15 Classical
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

abbrev PhysicalBin {κ : CConsts} {T : Stage} {k : ℕ} (PT : ProfiledTiling κ T k) :=
  Σ i : Fin PT.tiling.m, Bin PT.tiling i

theorem physical_bin_injective {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) :
    Function.Injective (fun D : PhysicalBin PT => D.2.1) := by
  intro D E hDE
  rcases D with ⟨i, D⟩
  rcases E with ⟨j, E⟩
  have hij : i = j := by
    by_contra hne
    have hDne : D.1 ≠ ∅ := by
      intro he
      have h2 := D.2
      rw [he] at h2
      exact (PT.tiling.P i).bins.bot_notMem (by rw [Finset.bot_eq_empty]; exact h2)
    obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hDne
    have hdis := Lane_q_s15_c2.clusterBin_sets_disjoint_of_patches hPT hne D E
    have hDE' : D.1 = E.1 := hDE
    exact Finset.disjoint_left.mp hdis hy (hDE' ▸ hy)
  subst j
  have hbin : D = E := Subtype.ext hDE
  subst E
  rfl

theorem physical_bin_probability_sum {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (g : ClusterGroupIndex PT) :
    (∑ D : PhysicalBin PT, clusterBinProbability PT hPT hm W g D.2.1) = 1 := by
  classical
  unfold clusterBinProbability
  rw [Finset.sum_comm]
  have hinner (D' : clusterBinType g) :
      (∑ D : PhysicalBin PT, if D'.1 = D.2.1 then
        (clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1) D' else 0) =
        (clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1) D' := by
    let d : PhysicalBin PT := ⟨g.1.1, D'⟩
    have hpred (D : PhysicalBin PT) : D'.1 = D.2.1 ↔ D = d := by
      constructor
      · intro h
        exact (physical_bin_injective PT hPT h).symm
      · intro h
        subst D
        rfl
    calc
      _ = ∑ D : PhysicalBin PT, if D = d then
          (clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1) D' else 0 := by
        apply Finset.sum_congr rfl
        intro D hD
        by_cases heq : D = d
        · simp only [if_pos heq, if_pos ((hpred D).mpr heq)]
        · simp only [if_neg heq, if_neg (mt (hpred D).mp heq)]
      _ = _ := by simp
  simp_rw [hinner]
  exact (clusterSolver PT hPT hm g.1.1).q_sum g.2 (historyOnSlice W g.1)

end HypercubeRamsey.Lane_sol_s15_c2
