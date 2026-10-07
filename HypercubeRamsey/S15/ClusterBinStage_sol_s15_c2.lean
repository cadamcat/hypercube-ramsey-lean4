import HypercubeRamsey.S15.ClusterNodes_sol_s15_transfer
import HypercubeRamsey.S15.Capacity

namespace HypercubeRamsey.Lane_sol_s15_c2

open HypercubeRamsey.S15 Classical Filter
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] Classical.propDecidable

theorem label_kernel_bin_gate {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (B D : ClusterBinAssignment PT)
    (F : ClusterInternalData PT → ℝ) :
    (clusterIndependentLabelKernel PT hPT hm W B).E
      (fun I => if clusterBinsOfInternal I = D then F I else 0) =
      if B = D then (clusterIndependentLabelKernel PT hPT hm W B).E F else 0 := by
  rw [Lane_sol_s15_transfer.independent_label_E_eq_word_E]
  by_cases hBD : B = D
  · rw [if_pos hBD, Lane_sol_s15_transfer.independent_label_E_eq_word_E]
    unfold FinLaw.E
    apply Finset.sum_congr rfl
    intro ys hys
    dsimp only
    have hpins : clusterBinsOfInternal (Lane_sol_s15_transfer.internalOfWordLabels B ys) = D := by
      change B = D
      exact hBD
    rw [if_pos hpins]
  · rw [if_neg hBD]
    have hpins (ys) : clusterBinsOfInternal (Lane_sol_s15_transfer.internalOfWordLabels B ys) ≠ D := by
      change B ≠ D
      exact hBD
    simp only [if_neg (hpins _)]
    simp [FinLaw.E]

theorem internal_kernel_bin_probability {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT) :
    (clusterInternalKernel PT hPT hm W).pr (fun I => clusterBinsOfInternal I = B) =
      (clusterIndependentBinKernel PT hPT hm W).w B := by
  rw [Lane_sol_s15_transfer.pr_eq_E_indicator,
    Lane_sol_s15_transfer.internal_kernel_eq_bin_label_E]
  have hgate (D : ClusterBinAssignment PT) :
      (clusterIndependentLabelKernel PT hPT hm W D).E
        (fun I => if clusterBinsOfInternal I = B then (1 : ℝ) else 0) = if D = B then 1 else 0 := by
    rw [label_kernel_bin_gate]
    simp [FinLaw.E, ← Finset.sum_mul, FinLaw.sum_one]
  have hfun : (fun D : ClusterBinAssignment PT =>
      (clusterIndependentLabelKernel PT hPT hm W D).E
        (fun I => if clusterBinsOfInternal I = B then (1 : ℝ) else 0)) =
      (fun D => if D = B then (1 : ℝ) else 0) := funext hgate
  rw [hfun]
  simp [FinLaw.E]

theorem internal_kernel_bin_failure_probability {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT)
    (A : ClusterInternalData PT → Prop) :
    (clusterInternalKernel PT hPT hm W).pr (fun I => clusterBinsOfInternal I = B ∧ A I) =
      (clusterIndependentBinKernel PT hPT hm W).w B *
        (clusterIndependentLabelKernel PT hPT hm W B).pr A := by
  rw [Lane_sol_s15_transfer.pr_eq_E_indicator,
    Lane_sol_s15_transfer.internal_kernel_eq_bin_label_E]
  have hgate (D : ClusterBinAssignment PT) :
      (clusterIndependentLabelKernel PT hPT hm W D).E
        (fun I => if clusterBinsOfInternal I = B ∧ A I then (1 : ℝ) else 0) =
      if D = B then (clusterIndependentLabelKernel PT hPT hm W D).pr A else 0 := by
    rw [Lane_sol_s15_transfer.pr_eq_E_indicator]
    have hsplit (I : ClusterInternalData PT) :
        (if clusterBinsOfInternal I = B ∧ A I then (1 : ℝ) else 0) =
        if clusterBinsOfInternal I = B then (if A I then 1 else 0) else 0 := by
      split_ifs <;> simp_all
    simp_rw [hsplit]
    exact label_kernel_bin_gate PT hPT hm W D B _
  have hfun : (fun D : ClusterBinAssignment PT =>
      (clusterIndependentLabelKernel PT hPT hm W D).E
        (fun I => if clusterBinsOfInternal I = B ∧ A I then (1 : ℝ) else 0)) =
      (fun D => if D = B then (clusterIndependentLabelKernel PT hPT hm W D).pr A else 0) := funext hgate
  rw [hfun]
  simp [FinLaw.E]

theorem bin_star_failure_eq {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT) (a : EvenPosition T k)
    (hB : 0 < (clusterIndependentBinKernel PT hPT hm W).w B) :
    clusterBinStarFailure PT hPT hm W B a =
      (clusterIndependentLabelKernel PT hPT hm W B).pr
        (fun I => clusterRowMass PT hPT hm W I a < 1 / 2) := by
  dsimp only [clusterBinStarFailure]
  rw [internal_kernel_bin_probability, internal_kernel_bin_failure_probability, if_pos hB]
  exact mul_div_cancel_left₀ _ hB.ne'

theorem bin_star_failure_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT) (a : EvenPosition T k) :
    0 ≤ clusterBinStarFailure PT hPT hm W B a := by
  dsimp only [clusterBinStarFailure]
  split_ifs with hB
  · exact div_nonneg (Finset.sum_nonneg fun I _ => by split_ifs; exact (clusterInternalKernel PT hPT hm W).nonneg I; exact le_rfl) hB.le
  · exact le_rfl

theorem bin_star_failure_mean {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k) :
    (clusterIndependentBinKernel PT hPT hm W).E (fun B => clusterBinStarFailure PT hPT hm W B a) =
      (clusterInternalKernel PT hPT hm W).pr (fun I => clusterRowMass PT hPT hm W I a < 1 / 2) := by
  rw [Lane_sol_s15_transfer.pr_eq_E_indicator,
    Lane_sol_s15_transfer.internal_kernel_eq_bin_label_E]
  unfold FinLaw.E
  apply Finset.sum_congr rfl
  intro B hB
  dsimp only
  by_cases hpos : 0 < (clusterIndependentBinKernel PT hPT hm W).w B
  · rw [bin_star_failure_eq PT hPT hm W B a hpos]
    rw [Lane_sol_s15_transfer.pr_eq_E_indicator]
    rfl
  · have hzero : (clusterIndependentBinKernel PT hPT hm W).w B = 0 :=
      le_antisymm (le_of_not_gt hpos) ((clusterIndependentBinKernel PT hPT hm W).nonneg B)
    simp [hzero]

theorem bin_star_failure_tail {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k)
    (hn : 0 < T.S.n k)
    (hmass : (clusterInternalKernel PT hPT hm W).pr
      (fun I => clusterRowMass PT hPT hm W I a < 1 / 2) ≤ (T.S.n k : ℝ) ^ (-(κ.R : ℝ))) :
    (clusterIndependentBinKernel PT hPT hm W).pr
      (fun B => (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2) < clusterBinStarFailure PT hPT hm W B a) ≤
      (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2) := by
  have hnR : (0 : ℝ) < T.S.n k := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2) := Real.rpow_pos_of_pos hnR _
  have h := Lane_q_s15_c3.finLaw_pr_markov (clusterIndependentBinKernel PT hPT hm W)
    (fun _ => True) (fun B => clusterBinStarFailure PT hPT hm W B a)
    (fun B _ => bin_star_failure_nonneg PT hPT hm W B a) _ hpos 1
  simp only [true_and, ite_true, pow_one] at h
  rw [bin_star_failure_mean] at h
  calc
    _ ≤ (clusterInternalKernel PT hPT hm W).pr
      (fun I => clusterRowMass PT hPT hm W I a < 1 / 2) /
        (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2) := h
    _ ≤ (T.S.n k : ℝ) ^ (-(κ.R : ℝ)) / (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2) :=
      div_le_div_of_nonneg_right hmass hpos.le
    _ = _ := by rw [← Real.rpow_sub hnR]; congr 1 <;> ring

theorem avoided_history_raw_positive {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (hp : 0 < (clusterHistoryLaw PT hPT hm).pr (clusterAlarmsAvoided PT hPT hm))
    (W : ClusterHistory PT hPT hm) (hW : (clusterAvoidedHistoryLaw PT hPT hm hp).w W ≠ 0) :
    0 < (clusterHistoryLaw PT hPT hm).w W := by
  have hraw : (clusterHistoryLaw PT hPT hm).w W ≠ 0 := by
    intro hz
    apply hW
    dsimp [clusterAvoidedHistoryLaw, FinLaw.cond]
    split_ifs <;> simp [hz]
  exact lt_of_le_of_ne ((clusterHistoryLaw PT hPT hm).nonneg W) (Ne.symm hraw)

structure BinLawOutput {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) where
  law : FinLaw (ClusterBinAssignment PT)
  good : ∀ B, law.w B ≠ 0 → clusterBinGood PT hPT hm W B
  comparison : ∀ F : ClusterBinAssignment PT → ℝ, (∀ B, 0 ≤ F B) →
    ∀ S : Finset (ClusterGroupIndex PT), ClusterBinDependsOn F S →
      (S.card : ℝ) ≤ (T.S.n k : ℝ) ^ 3 →
        law.E F ≤ (1 + 1 / (T.S.n k : ℝ)) * (clusterIndependentBinKernel PT hPT hm W).E F

theorem binStage_reference_positive {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (BS : ClusterBinStage PT hPT hm) (hn : 0 < T.S.n k)
    (W : ClusterHistory PT hPT hm) (hW : BS.historyLaw.w W ≠ 0)
    (hload : clusterHistoryLoad PT hPT hm W)
    (B : ClusterBinAssignment PT) (hB : (BS.binLaw W).w B ≠ 0) :
    0 < (clusterIndependentBinKernel PT hPT hm W).w B := by
  have hnR : (1 : ℝ) ≤ T.S.n k := by exact_mod_cast hn
  have hcoef : 0 < 1 + 1 / (T.S.n k : ℝ) := by positivity
  have hBpos : 0 < (BS.binLaw W).w B := lt_of_le_of_ne ((BS.binLaw W).nonneg B) (Ne.symm hB)
  have hq (g : ClusterGroupIndex PT) :
      0 < (clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1) (B g) := by
    let F : ClusterBinAssignment PT → ℝ := fun D => if D g = B g then 1 else 0
    have hF (D) : 0 ≤ F D := by dsimp [F]; split_ifs <;> norm_num
    have hdep : ClusterBinDependsOn F {g} := by
      intro D D' hDD
      dsimp [F]
      rw [hDD g (Finset.mem_singleton_self g)]
    have hcard : (({g} : Finset (ClusterGroupIndex PT)).card : ℝ) ≤ (T.S.n k : ℝ) ^ 3 := by
      simp only [Finset.card_singleton, Nat.cast_one]
      exact one_le_pow₀ hnR
    have hcomp := BS.local_upper_comparison W hW hload F hF {g} hdep hcard
    have hraw : (clusterIndependentBinKernel PT hPT hm W).E F =
        (clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1) (B g) := by
      let laws (g' : ClusterGroupIndex PT) : FinLaw (clusterBinType g') :=
        ⟨(clusterSolver PT hPT hm g'.1.1).q g'.2 (historyOnSlice W g'.1),
          (clusterSolver PT hPT hm g'.1.1).q_nonneg _ _,
          (clusterSolver PT hPT hm g'.1.1).q_sum _ _⟩
      have hE := Lane_sol_s15_transfer.E_pi_coord laws g
        (fun D : clusterBinType g => if D = B g then (1 : ℝ) else 0)
      calc
        _ = (laws g).E (fun D => if D = B g then (1 : ℝ) else 0) := by
          convert hE using 1
          rfl
        _ = _ := by simp [FinLaw.E, laws]
    rw [hraw] at hcomp
    have hterm : (BS.binLaw W).w B ≤ (BS.binLaw W).E F := by
      unfold FinLaw.E
      have h := Finset.single_le_sum (s := Finset.univ) (f := fun D => (BS.binLaw W).w D * F D)
        (fun D _ => mul_nonneg ((BS.binLaw W).nonneg D) (hF D)) (Finset.mem_univ B)
      simpa [F] using h
    have hprod := lt_of_lt_of_le hBpos (hterm.trans hcomp)
    exact (mul_pos_iff_of_pos_left hcoef).mp hprod
  change 0 < ∏ g : ClusterGroupIndex PT,
    (clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1) (B g)
  exact Finset.prod_pos fun g _ => hq g

end HypercubeRamsey.Lane_sol_s15_c2
