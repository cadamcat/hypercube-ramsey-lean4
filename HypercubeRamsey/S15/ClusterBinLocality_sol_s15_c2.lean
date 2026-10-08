import HypercubeRamsey.S15.ClusterBinStage_sol_s15_c2
import HypercubeRamsey.S15.ClusterSeparation_sol_s15_transfer

namespace HypercubeRamsey.Lane_sol_s15_c2

open HypercubeRamsey.S15 OAI.HypercubeRamsey Classical Filter
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def starGroupQueries {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) (a : EvenPosition T k) :
    Finset (ClusterGroupIndex PT) :=
  (Lane_q_s15_direct.star a).image (clusterGroupIndexAt PT hPT hm)

noncomputable def starWordQueries {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) (a : EvenPosition T k) :
    Finset (ClusterConsultation PT) :=
  Lane_sol_s15_transfer.rowWordQueries PT hPT hm a ∪
    ((clusterBulkNeighbours PT hPT a ∪ clusterCrossingNeighbours PT hPT a).image
      (Lane_sol_s15_transfer.wordAtOdd PT hPT hm))

theorem starGroupQueries_card_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) (a : EvenPosition T k) :
    (starGroupQueries PT hPT hm a).card ≤ T.S.n k :=
  Finset.card_image_le.trans (Lane_q_s15_direct.star_card_le a)

theorem starGroupQueries_incidence_card_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) (g : ClusterGroupIndex PT) :
    (Finset.univ.filter fun a : EvenPosition T k => g ∈ starGroupQueries PT hPT hm a).card ≤
      2 * (PT.tiling.P g.1.1).h * T.S.n k := by
  let roles := Finset.univ.filter fun b : OddPosition T k => clusterGroupIndexAt PT hPT hm b = g
  have hsub : (Finset.univ.filter fun a : EvenPosition T k => g ∈ starGroupQueries PT hPT hm a) ⊆
      roles.biUnion Lane_q_s15_direct.starIncidence := by
    intro a ha
    obtain ⟨b, hb, hbg⟩ := Finset.mem_image.mp (Finset.mem_filter.mp ha).2
    exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbg⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩⟩
  calc
    _ ≤ (roles.biUnion Lane_q_s15_direct.starIncidence).card := Finset.card_le_card hsub
    _ ≤ ∑ b ∈ roles, (Lane_q_s15_direct.starIncidence b).card := Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ roles, T.S.n k := Finset.sum_le_sum fun b _ => Lane_q_s15_direct.star_incidence_card_le b
    _ = roles.card * T.S.n k := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (Lane_q_s15_c2.clusterGroupRoleCount_le_twiceHeight PT hPT hm g)

theorem word_query_group_mem_star {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) {c : ClusterConsultation PT} (hc : c ∈ starWordQueries PT hPT hm a) :
    Lane_sol_s15_transfer.wordGroup PT hPT hm c ∈ starGroupQueries PT hPT hm a := by
  rcases Finset.mem_union.mp hc with hc | hc
  · have hg := Lane_sol_s15_transfer.row_word_group_mem_core PT hPT hm a hc
    obtain ⟨b, hb, hbg⟩ := Finset.mem_image.mp hg
    exact Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2.1⟩, hbg⟩
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc
    have hab : Adjacent a b := by
      rcases Finset.mem_union.mp hb with hb | hb <;> exact (Finset.mem_filter.mp hb).2.1
    exact Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩, rfl⟩

theorem row_weight_word_depends {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT)
    (a : EvenPosition T k) (x : Fin (T.S.N k)) :
    FinProb.DependsOn
      (fun ys => clusterRowWeight PT hPT hm W (Lane_sol_s15_transfer.internalOfWordLabels B ys) a x)
      (starWordQueries PT hPT hm a) := by
  intro ys ys' hys
  have hσ : clusterSigma PT hPT hm W (Lane_sol_s15_transfer.internalOfWordLabels B ys) a x =
      clusterSigma PT hPT hm W (Lane_sol_s15_transfer.internalOfWordLabels B ys') a x := by
    let s := clusterSliceAt PT hPT a.1
    let v : EvenRole PT.tiling s.1 := clusterCenterRole PT hPT hm a
    change (clusterSolver PT hPT hm s.1).σ v (historyOnSlice W s)
      (fun l => ys ⟨s, flipPos v.1 l⟩) x =
      (clusterSolver PT hPT hm s.1).σ v (historyOnSlice W s) (fun l => ys' ⟨s, flipPos v.1 l⟩) x
    apply congrArg (fun labs => (clusterSolver PT hPT hm s.1).σ v (historyOnSlice W s) labs x)
    funext l
    exact hys _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩))
  unfold clusterRowWeight
  dsimp only
  rw [hσ]
  congr 1
  apply Finset.prod_congr rfl
  intro b hb
  have hlabel := hys (Lane_sol_s15_transfer.wordAtOdd PT hPT hm b)
    (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, hb, rfl⟩))
  dsimp [clusterFactor, Lane_sol_s15_transfer.internalOfWordLabels]
  change (if 0 < clusterDegree PT hPT hm W b x then
    hit (T.S.E k) PT.tiling.c x (ys (Lane_sol_s15_transfer.wordAtOdd PT hPT hm b)) / clusterDegree PT hPT hm W b x else 0) = _
  rw [hlabel]
  rfl

theorem reference_mass_failure_bin_depends {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k) :
    ClusterBinDependsOn (fun B => (clusterIndependentLabelKernel PT hPT hm W B).pr
      (fun I => clusterRowMass PT hPT hm W I a < 1 / 2)) (starGroupQueries PT hPT hm a) := by
  intro B B' hBB
  dsimp only
  rw [Lane_sol_s15_transfer.pr_eq_E_indicator, Lane_sol_s15_transfer.pr_eq_E_indicator,
    Lane_sol_s15_transfer.independent_label_E_eq_word_E, Lane_sol_s15_transfer.independent_label_E_eq_word_E]
  let F := fun ys => if clusterRowMass PT hPT hm W (Lane_sol_s15_transfer.internalOfWordLabels B ys) a < 1 / 2 then (1 : ℝ) else 0
  have hdep : FinProb.DependsOn F (starWordQueries PT hPT hm a) := by
    intro ys ys' hys
    have hmass : clusterRowMass PT hPT hm W (Lane_sol_s15_transfer.internalOfWordLabels B ys) a =
        clusterRowMass PT hPT hm W (Lane_sol_s15_transfer.internalOfWordLabels B ys') a := by
      unfold clusterRowMass
      apply Finset.sum_congr rfl
      intro x hx
      exact row_weight_word_depends PT hPT hm W B a x ys ys' hys
    simp only [F, hmass]
  have h := Lane_sol_s15_transfer.E_pi_congr_on
    (Lane_sol_s15_transfer.wordLabelLaw PT hPT hm W B)
    (Lane_sol_s15_transfer.wordLabelLaw PT hPT hm W B') (starWordQueries PT hPT hm a) F hdep
    (by
      intro c hc y
      have hg := hBB _ (word_query_group_mem_star PT hPT hm a hc)
      dsimp [Lane_sol_s15_transfer.wordLabelLaw]
      rw [hg])
  exact h

end HypercubeRamsey.Lane_sol_s15_c2
