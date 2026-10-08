import HypercubeRamsey.S15.ClusterBinSampler_sol_s15_c2

namespace HypercubeRamsey.Lane_sol_s15_c2

open HypercubeRamsey.S15 Classical
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem indicator_forall_eq_prod {I : Type*} [DecidableEq I] (S : Finset I) (p : I → Prop) [DecidablePred p] :
    (if ∀ i ∈ S, p i then (1 : ℝ) else 0) = ∏ i ∈ S, if p i then 1 else 0 := by
  classical
  by_cases h : ∀ i ∈ S, p i
  · rw [if_pos h]
    symm
    exact Finset.prod_eq_one fun i hi => by simp [h i hi]
  · rw [if_neg h]
    obtain ⟨i, hi, hp⟩ : ∃ i ∈ S, ¬ p i := by
      by_contra hnot
      apply h
      intro i hi
      by_contra hp
      exact hnot ⟨i, hi, hp⟩
    symm
    exact Finset.prod_eq_zero hi (by simp [hp])

theorem fixed_physical_bins_probability {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (A : Finset (ClusterGroupIndex PT))
    (D : Finset (Fin (T.S.N k))) :
    (clusterIndependentBinKernel PT hPT hm W).pr (fun B => ∀ g ∈ A, (B g).1 = D) =
      ∏ g ∈ A, clusterBinProbability PT hPT hm W g D := by
  classical
  let laws (g : ClusterGroupIndex PT) : FinLaw (clusterBinType g) :=
    ⟨(clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1),
      (clusterSolver PT hPT hm g.1.1).q_nonneg _ _,
      (clusterSolver PT hPT hm g.1.1).q_sum _ _⟩
  let f (g : ClusterGroupIndex PT) (B : clusterBinType g) : ℝ := if B.1 = D then 1 else 0
  have hKernel : clusterIndependentBinKernel PT hPT hm W = FinLaw.pi laws := rfl
  rw [hKernel, Lane_sol_s15_transfer.pr_eq_E_indicator]
  have hprod := Lane_q_s15_direct.finLaw_pi_E_finset_product laws A f
  calc
    _ = (FinLaw.pi laws).E (fun B => ∏ g ∈ A, f g (B g)) := by
      unfold FinLaw.E
      apply Finset.sum_congr rfl
      intro B hB
      dsimp only
      apply congrArg (fun z : ℝ => (FinLaw.pi laws).w B * z)
      have h := indicator_forall_eq_prod A
        (fun g : ClusterGroupIndex PT => (show Bin PT.tiling g.1.1 from B g).1 = D)
      by_cases hall : ∀ g ∈ A, (B g).1 = D
      · simpa only [if_pos hall, f] using h
      · simpa only [if_neg hall, f] using h
    _ = ∏ g ∈ A, (laws g).E (f g) := hprod
    _ = _ := by
      apply Finset.prod_congr rfl
      intro g hg
      unfold FinLaw.E clusterBinProbability
      apply Finset.sum_congr rfl
      intro B hB
      dsimp [f, laws]
      split_ifs <;> simp

theorem certificate_probability {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (c : CapacityCertificate PT) :
    (clusterIndependentBinKernel PT hPT hm W).pr (certificateEvent PT hPT hm W c) =
      if certificateActive PT hPT hm W c then
        ∏ g ∈ c.2.2, clusterBinProbability PT hPT hm W g c.1.2.1 else 0 := by
  classical
  by_cases hc : certificateActive PT hPT hm W c
  · rw [if_pos hc]
    have hpred : certificateEvent PT hPT hm W c =
        (fun B => ∀ g ∈ c.2.2, (B g).1 = c.1.2.1) := by
      funext B
      apply propext
      simp only [certificateEvent, hc, true_and]
    rw [hpred]
    exact fixed_physical_bins_probability PT hPT hm W c.2.2 c.1.2.1
  · simp [FinLaw.pr, certificateEvent, hc]

end HypercubeRamsey.Lane_sol_s15_c2
