import HypercubeRamsey.S15.ClusterLabelBasics_sol_s15_c2
import HypercubeRamsey.S15.ClusterBinStage_sol_s15_c2

namespace HypercubeRamsey.Lane_sol_s15_c2

open HypercubeRamsey.S15 Classical Filter
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem expect_const {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (c : ℝ) :
    P.E (fun _ => c) = c := by
  unfold FinLaw.E
  rw [← Finset.sum_mul, P.sum_one, one_mul]

structure LabelLawOutput {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT) where
  preLaw : FinLaw (ClusterInternalData PT)
  law : FinLaw (ClusterInternalData PT)
  pins : ∀ I, law.w I ≠ 0 → clusterBinsOfInternal I = B
  singleton : ∀ b y, preLaw.pr (fun I => clusterLabelFromInternal (hPT := hPT) hm I b = y) =
    (clusterSolver PT hPT hm (patchAt PT hPT b.1)).U (clusterGroupIndexAt PT hPT hm b).2
      (historyOnSlice W (clusterSliceAt PT hPT b.1)) (B (clusterGroupIndexAt PT hPT hm b)) y
  preComparison : ∀ F : ClusterInternalData PT → ℝ, (∀ I, 0 ≤ F I) →
    ∀ S : Finset (OddPosition T k), ClusterLabelDependsOn hPT hm F S →
      (S.card : ℝ) ≤ (T.S.n k : ℝ) ^ 2 → ClusterLabelQueryOK PT hPT hm B S →
        preLaw.E F ≤ clusterLabelError PT hPT hm B S * (clusterIndependentLabelKernel PT hPT hm W B).E F
  comparison : ∀ F : ClusterInternalData PT → ℝ, (∀ I, 0 ≤ F I) →
    ∀ S : Finset (OddPosition T k), ClusterLabelDependsOn hPT hm F S →
      (S.card : ℝ) ≤ (T.S.n k : ℝ) ^ 2 → law.E F ≤ 2 * preLaw.E F
  supported : ∀ I, law.w I ≠ 0 → ∀ b,
    clusterLabelFromInternal (hPT := hPT) hm I b ∈ (PT.tiling.P (patchAt PT hPT b.1)).Y
  injective : ∀ I, law.w I ≠ 0 → Function.Injective (clusterLabelFromInternal (hPT := hPT) hm I)
  mass : ∀ I, law.w I ≠ 0 → ∀ a, (1 / 2 : ℝ) ≤ clusterRowMass PT hPT hm W I a

private theorem event_weight_zero {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (A : Ω → Prop)
    (hA : P.pr A = 0) (ω : Ω) (hω : A ω) : P.w ω = 0 := by
  have hle : P.w ω ≤ P.pr A := by
    unfold FinLaw.pr
    have h := Finset.single_le_sum (s := Finset.univ) (f := fun x => if A x then P.w x else 0)
      (fun x _ => by split_ifs; exact P.nonneg x; exact le_rfl) (Finset.mem_univ ω)
    simpa only [if_pos hω] using h
  exact le_antisymm (hA ▸ hle) (P.nonneg ω)

theorem independent_label_pins {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT)
    (I : ClusterInternalData PT) (hI : (clusterIndependentLabelKernel PT hPT hm W B).w I ≠ 0) :
    clusterBinsOfInternal I = B := by
  have hzero : (clusterIndependentLabelKernel PT hPT hm W B).pr
      (fun I => clusterBinsOfInternal I ≠ B) = 0 := by
    rw [Lane_sol_s15_transfer.pr_eq_E_indicator, Lane_sol_s15_transfer.independent_label_E_eq_word_E]
    have hpins (ys : ClusterConsultation PT → Fin (T.S.N k)) :
        clusterBinsOfInternal (Lane_sol_s15_transfer.internalOfWordLabels B ys) = B := rfl
    simp only [hpins, ne_eq, not_true_eq_false, ite_false]
    simp [FinLaw.E]
  by_contra hnot
  exact hI (event_weight_zero _ _ hzero I hnot)

set_option maxHeartbeats 400000 in
theorem sample_of_label_outputs {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (BS : ClusterBinStage PT hPT hm) (hn : 0 < T.S.n k)
    (hout : ∀ W, BS.historyLaw.w W ≠ 0 → clusterHistoryLoad PT hPT hm W →
      ∀ B, (BS.binLaw W).w B ≠ 0 → Nonempty (LabelLawOutput PT hPT hm W B)) :
    Nonempty (ClusterSample PT hPT hm) := by
  classical
  let good (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT) :=
    BS.historyLaw.w W ≠ 0 ∧ clusterHistoryLoad PT hPT hm W ∧ (BS.binLaw W).w B ≠ 0
  let output (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT) (h : good W B) :=
    Classical.choice (hout W h.1 h.2.1 B h.2.2)
  let pre (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT) :=
    if h : good W B then (output W B h).preLaw else clusterIndependentLabelKernel PT hPT hm W B
  let K (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT) :=
    if h : good W B then (output W B h).law else clusterIndependentLabelKernel PT hPT hm W B
  let Q := FinLaw.bind BS.historyLaw BS.binLaw
  let P := FinLaw.bind Q (fun wb => K wb.1 wb.2)
  let A : ((ClusterHistory PT hPT hm × ClusterBinAssignment PT) × ClusterInternalData PT) → Prop :=
    fun ω => clusterBinsOfInternal ω.2 = ω.1.2
  have hPins (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT) (I : ClusterInternalData PT)
      (hI : (K W B).w I ≠ 0) : clusterBinsOfInternal I = B := by
    by_cases h : good W B
    · exact (output W B h).pins I (by simpa only [K, dif_pos h] using hI)
    · exact independent_label_pins PT hPT hm W B I (by simpa only [K, dif_neg h] using hI)
  have hA (ω) (hω : ¬ A ω) : P.w ω = 0 := by
    have hI : (K ω.1.1 ω.1.2).w ω.2 = 0 := by
      by_contra hI
      exact hω (hPins _ _ _ hI)
    simp [P, FinLaw.bind, hI]
  letI : DecidablePred A := fun ω => Classical.propDecidable (A ω)
  let Ω := {ω // A ω}
  let law : FinLaw Ω := restrictLaw P A hA
  have hsupport (ω : Ω) (hω : law.w ω ≠ 0) :
      BS.historyLaw.w ω.1.1.1 ≠ 0 ∧ (BS.binLaw ω.1.1.1).w ω.1.1.2 ≠ 0 ∧
        (K ω.1.1.1 ω.1.1.2).w ω.1.2 ≠ 0 := by
    change (BS.historyLaw.w ω.1.1.1 * (BS.binLaw ω.1.1.1).w ω.1.1.2) *
      (K ω.1.1.1 ω.1.1.2).w ω.1.2 ≠ 0 at hω
    exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hω).1).1,
      (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hω).1).2, (mul_ne_zero_iff.mp hω).2⟩
  have hOutSupport (ω : Ω) (hω : law.w ω ≠ 0) (hload : clusterHistoryLoad PT hPT hm ω.1.1.1) :
      (output ω.1.1.1 ω.1.1.2 ⟨(hsupport ω hω).1, hload, (hsupport ω hω).2.1⟩).law.w ω.1.2 ≠ 0 := by
    have hg : good ω.1.1.1 ω.1.1.2 := ⟨(hsupport ω hω).1, hload, (hsupport ω hω).2.1⟩
    simpa only [K, dif_pos hg] using (hsupport ω hω).2.2
  have hMarginal (W B) : law.pr (fun ω => ω.1.1.1 = W ∧ ω.1.1.2 = B) = Q.pr (fun wb => wb = (W, B)) := by
    let Fraw : ((ClusterHistory PT hPT hm × ClusterBinAssignment PT) × ClusterInternalData PT) → ℝ :=
      fun ω => @ite ℝ (ω.1.1 = W ∧ ω.1.2 = B) (Classical.propDecidable _) 1 0
    have hR := restrictLaw_E P A hA Fraw
    rw [Lane_sol_s15_transfer.pr_eq_E_indicator]
    change law.E (fun ω => Fraw ω.1) = _
    rw [hR, Lane_q_s15_c2.expect_bind, Lane_sol_s15_transfer.pr_eq_E_indicator]
    have hconst (wb) : (K wb.1 wb.2).E
        (fun I => Fraw (wb, I)) = @ite ℝ (wb = (W, B)) (Classical.propDecidable _) 1 0 := by
      have h := expect_const (K wb.1 wb.2) (@ite ℝ (wb.1 = W ∧ wb.2 = B) (Classical.propDecidable _) 1 0)
      by_cases heq : wb = (W, B)
      · have hp : wb.1 = W ∧ wb.2 = B := Prod.ext_iff.mp heq
        simpa only [Fraw, if_pos hp, if_pos heq] using h
      · have hp : ¬ (wb.1 = W ∧ wb.2 = B) := fun hp => heq (Prod.ext hp.1 hp.2)
        simpa only [Fraw, if_neg hp, if_neg heq] using h
    simp_rw [hconst]
  have hLoadPr : law.pr (fun ω => clusterHistoryLoad PT hPT hm ω.1.1.1) =
      BS.historyLaw.pr (clusterHistoryLoad PT hPT hm) := by
    let Fraw : ((ClusterHistory PT hPT hm × ClusterBinAssignment PT) × ClusterInternalData PT) → ℝ :=
      fun ω => @ite ℝ (clusterHistoryLoad PT hPT hm ω.1.1) (Classical.propDecidable _) 1 0
    have hR := restrictLaw_E P A hA Fraw
    rw [Lane_sol_s15_transfer.pr_eq_E_indicator]
    change law.E (fun ω => Fraw ω.1) = _
    rw [hR, Lane_q_s15_c2.expect_bind]
    have hK (wb) : (K wb.1 wb.2).E
        (fun I => Fraw (wb, I)) =
        @ite ℝ (clusterHistoryLoad PT hPT hm wb.1) (Classical.propDecidable _) 1 0 := by
      by_cases hc : clusterHistoryLoad PT hPT hm wb.1
      · simp only [Fraw, if_pos hc]
        exact expect_const (K wb.1 wb.2) 1
      · simp only [Fraw, if_neg hc]
        exact expect_const (K wb.1 wb.2) 0
    simp_rw [hK]
    rw [Lane_q_s15_c2.expect_bind]
    have hB (W) : (BS.binLaw W).E
        (fun _ => @ite ℝ (clusterHistoryLoad PT hPT hm W) (Classical.propDecidable _) 1 0) =
        @ite ℝ (clusterHistoryLoad PT hPT hm W) (Classical.propDecidable _) 1 0 := expect_const _ _
    simp_rw [hB]
    exact (Lane_sol_s15_transfer.pr_eq_E_indicator _ _).symm
  refine ⟨{
    Outcome := Ω
    law := law
    binStage := BS
    history := fun ω => ω.1.1.1
    internal := fun ω => ω.1.2
    bins := fun ω => ω.1.1.2
    label := fun ω => clusterLabelFromInternal (hPT := hPT) hm ω.1.2
    preLabelKernel := pre
    labelKernel := K
    label_disintegration := restrictLaw_map_val P A hA
    prelabel_singleton := ?_
    prelabel_upper_comparison := ?_
    label_local_upper_comparison := ?_
    row := fun ω => clusterRowWeight PT hPT hm ω.1.1.1 ω.1.2
    historyLoad := fun ω => clusterHistoryLoad PT hPT hm ω.1.1.1
    history_eq := fun _ => Iff.rfl
    history_load_probability := ?_
    bins_eq := ?_
    bin_stage_marginal_eq := hMarginal
    label_eq := fun _ _ => rfl
    label_supported := ?_
    row_eq := fun _ _ _ => rfl
    injective_on_support := ?_
    row_nonneg := ?_
    mass_gate := ?_
    row_support := ?_
    common_neighbour := ?_ }⟩
  · intro W hW hload B hB b y
    have hg : good W B := ⟨hW, hload, hB⟩
    simpa only [pre, dif_pos hg] using (output W B hg).singleton b y
  · intro W hW hload B hB F hF S hdep hcard hquery
    have hg : good W B := ⟨hW, hload, hB⟩
    simpa only [pre, dif_pos hg] using
      (output W B hg).preComparison F hF S hdep hcard hquery
  · intro W hW hload B hB F hF S hdep hcard
    have hg : good W B := ⟨hW, hload, hB⟩
    simpa only [pre, K, dif_pos hg] using
      (output W B hg).comparison F hF S hdep hcard
  · rw [hLoadPr]
    convert BS.history_load_probability using 1 <;> norm_num
  · intro ω g
    exact (congrFun ω.2 g).symm
  · intro ω hω hload b
    exact (output ω.1.1.1 ω.1.1.2 ⟨(hsupport ω hω).1, hload, (hsupport ω hω).2.1⟩).supported
      ω.1.2 (hOutSupport ω hω hload) b
  · intro ω hω hload
    exact (output ω.1.1.1 ω.1.1.2 ⟨(hsupport ω hω).1, hload, (hsupport ω hω).2.1⟩).injective
      ω.1.2 (hOutSupport ω hω hload)
  · intro ω a x
    exact row_weight_nonneg PT hPT hm ω.1.1.1 ω.1.2 a x
  · intro ω hω hload a
    exact (output ω.1.1.1 ω.1.1.2 ⟨(hsupport ω hω).1, hload, (hsupport ω hω).2.1⟩).mass
      ω.1.2 (hOutSupport ω hω hload) a
  · intro ω hω hload a x hx
    have hraw : 0 < (clusterHistoryLaw PT hPT hm).w ω.1.1.1 := by
      apply avoided_history_raw_positive PT hPT hm BS.history_positive _
      rw [← BS.historyLaw_eq]
      exact (hsupport ω hω).1
    exact Lane_sol_s15_load.clusterSigma_support_envelope PT hPT hm _ hraw _ a x
      (row_weight_sigma_ne_zero PT hPT hm _ _ a x hx)
  · intro ω hω hload a x hx b hab
    exact row_weight_common_neighbour PT hPT hm hn _ _ a x hx b hab

end HypercubeRamsey.Lane_sol_s15_c2
