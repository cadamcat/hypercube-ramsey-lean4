import HypercubeRamsey.S15.ClusterLabelGeometry_sol_s15_c2
import HypercubeRamsey.S15.ClusterLabelBasics_sol_s15_c2

namespace HypercubeRamsey.Lane_sol_s15_c2

open HypercubeRamsey.S15 Classical
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem law_ext {Ω : Type*} [Fintype Ω] (P Q : FinLaw Ω) (h : P.w = Q.w) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

theorem selected_coordinates_cylinder {V R X : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq R] [Fintype X] [DecidableEq X]
    (P : V → FinLaw X) (f : R → V) (hf : Function.Injective f) (S : Finset R) (ys : R → X) :
    (FinLaw.pi P).pr (fun ω => ∀ r ∈ S, ω (f r) = ys r) = ∏ r ∈ S, (P (f r)).w (ys r) := by
  classical
  let F : R → (V → X) → ℝ := fun r ω => if ω (f r) = ys r then 1 else 0
  have hdep (r : R) : FinProb.DependsOn (F r) {f r} := by
    intro ω ω' hω
    dsimp [F]
    rw [hω (f r) (Finset.mem_singleton_self _)]
  have hdis : ∀ r ∈ S, ∀ t ∈ S, r ≠ t → Disjoint ({f r} : Finset V) {f t} := by
    intro r hr t ht hrt
    apply Finset.disjoint_left.mpr
    intro v hvr hvt
    have heq : f r = f t := (Finset.mem_singleton.mp hvr).symm.trans (Finset.mem_singleton.mp hvt)
    exact hrt (hf heq)
  have hprod := Lane_sol_s15_transfer.E_pi_prod_of_disjoint P S F (fun r => {f r})
    (fun r _ => hdep r) hdis
  have hind (ω : V → X) : (if ∀ r ∈ S, ω (f r) = ys r then (1 : ℝ) else 0) = ∏ r ∈ S, F r ω := by
    by_cases hall : ∀ r ∈ S, ω (f r) = ys r
    · rw [if_pos hall]
      symm
      exact Finset.prod_eq_one fun r hr => by simp [F, hall r hr]
    · rw [if_neg hall]
      obtain ⟨r, hr, hnot⟩ : ∃ r ∈ S, ω (f r) ≠ ys r := by
        by_contra hnot
        apply hall
        intro r hr
        by_contra hne
        exact hnot ⟨r, hr, hne⟩
      symm
      exact Finset.prod_eq_zero hr (by simp [F, hnot])
  have hcoord (r : R) : (FinLaw.pi P).E (F r) = (P (f r)).w (ys r) := by
    have h := Lane_sol_s15_transfer.E_pi_coord P (f r) (fun x => if x = ys r then (1 : ℝ) else 0)
    calc
      _ = (P (f r)).E (fun x => if x = ys r then (1 : ℝ) else 0) := h
      _ = _ := by simp [FinLaw.E]
  rw [Lane_sol_s15_transfer.pr_eq_E_indicator]
  have hE : (FinLaw.pi P).E (fun ω => @ite ℝ (∀ r ∈ S, ω (f r) = ys r) (Classical.propDecidable _) 1 0) =
      (FinLaw.pi P).E (fun ω => ∏ r ∈ S, F r ω) := by
    unfold FinLaw.E
    apply Finset.sum_congr rfl
    intro ω hω
    dsimp only
    apply congrArg (fun z : ℝ => (FinLaw.pi P).w ω * z)
    have h := hind ω
    by_cases hall : ∀ r ∈ S, ω (f r) = ys r
    · simpa only [if_pos hall] using h
    · simpa only [if_neg hall] using h
  rw [hE, hprod]
  exact Finset.prod_congr rfl (fun r _ => hcoord r)

theorem map_pi_selected_coordinates {V R X : Type*} [Fintype V] [DecidableEq V]
    [Fintype R] [DecidableEq R] [Fintype X] [DecidableEq X]
    (P : V → FinLaw X) (f : R → V) (hf : Function.Injective f) :
    FinLaw.map (FinLaw.pi P) (fun ω r => ω (f r)) = FinLaw.pi (fun r => P (f r)) := by
  classical
  apply law_ext
  funext ys
  have h := selected_coordinates_cylinder P f hf Finset.univ ys
  have hpred : (fun ω : V → X => (fun r => ω (f r)) = ys) =
      (fun ω => ∀ r ∈ (Finset.univ : Finset R), ω (f r) = ys r) := by
    funext ω
    apply propext
    simp only [funext_iff, Finset.mem_univ, forall_const]
  change (∑ ω : V → X, if (fun r => ω (f r)) = ys then (FinLaw.pi P).w ω else 0) = _
  have hpr : (∑ ω : V → X, if (fun r => ω (f r)) = ys then (FinLaw.pi P).w ω else 0) =
      (FinLaw.pi P).pr (fun ω => (fun r => ω (f r)) = ys) := by
    unfold FinLaw.pr
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases h : (fun r => ω (f r)) = ys <;> simp [h]
  rw [hpr]
  rw [hpred]
  exact h

noncomputable def oddLabelAtWord {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (ys : OddAssignment T k) (c : ClusterConsultation PT) : Fin (T.S.N k) :=
  if h : ∃ b : OddPosition T k, Lane_sol_s15_transfer.wordAtOdd PT hPT hm b = c then
    ys (Classical.choose h) else ⟨0, T.S.N_pos k⟩

noncomputable def internalOfOddLabels {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (B : ClusterBinAssignment PT) (ys : OddAssignment T k) : ClusterInternalData PT :=
  fun s => (fun g => (show Bin PT.tiling s.1 from B ⟨s, g⟩),
    fun z => oddLabelAtWord PT hPT hm ys ⟨s, z⟩)

theorem internalOfOddLabels_pins {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (B : ClusterBinAssignment PT) (ys : OddAssignment T k) :
    clusterBinsOfInternal (internalOfOddLabels PT hPT hm B ys) = B := rfl

theorem internalOfOddLabels_label {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (B : ClusterBinAssignment PT) (ys : OddAssignment T k) (b : OddPosition T k) :
    clusterLabelFromInternal (hPT := hPT) hm (internalOfOddLabels PT hPT hm B ys) b = ys b := by
  classical
  have hex : ∃ c : OddPosition T k, Lane_sol_s15_transfer.wordAtOdd PT hPT hm c =
      Lane_sol_s15_transfer.wordAtOdd PT hPT hm b := ⟨b, rfl⟩
  have hchoose : Classical.choose hex = b := wordAtOdd_injective PT hPT hm (Classical.choose_spec hex)
  change oddLabelAtWord PT hPT hm ys (Lane_sol_s15_transfer.wordAtOdd PT hPT hm b) = ys b
  unfold oddLabelAtWord
  rw [dif_pos hex, hchoose]

set_option maxHeartbeats 400000 in
theorem independent_label_E_eq_odd_E {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT)
    (F : ClusterInternalData PT → ℝ) (S : Finset (OddPosition T k))
    (hF : ClusterLabelDependsOn hPT hm F S) :
    (clusterIndependentLabelKernel PT hPT hm W B).E F =
      (FinLaw.pi (oddLabelLaw PT hPT hm W B)).E
        (fun ys => F (internalOfOddLabels PT hPT hm B ys)) := by
  classical
  let P := Lane_sol_s15_transfer.wordLabelLaw PT hPT hm W B
  let select : (ClusterConsultation PT → Fin (T.S.N k)) → OddAssignment T k :=
    fun ys b => ys (Lane_sol_s15_transfer.wordAtOdd PT hPT hm b)
  have hMap : FinLaw.map (FinLaw.pi P) select = FinLaw.pi (oddLabelLaw PT hPT hm W B) := by
    rw [map_pi_selected_coordinates P (Lane_sol_s15_transfer.wordAtOdd PT hPT hm)
      (wordAtOdd_injective PT hPT hm)]
    rfl
  have hpoint (ys : ClusterConsultation PT → Fin (T.S.N k)) :
      F (Lane_sol_s15_transfer.internalOfWordLabels B ys) =
        F (internalOfOddLabels PT hPT hm B (select ys)) := by
    apply hF
    intro b hb
    change ys (Lane_sol_s15_transfer.wordAtOdd PT hPT hm b) = _
    rw [internalOfOddLabels_label]
  rw [Lane_sol_s15_transfer.independent_label_E_eq_word_E]
  calc
    _ = (FinLaw.pi P).E (fun ys => F (internalOfOddLabels PT hPT hm B (select ys))) := by
      unfold FinLaw.E
      apply Finset.sum_congr rfl
      intro ys hys
      dsimp only
      rw [hpoint ys]
    _ = (FinLaw.map (FinLaw.pi P) select).E (fun ys => F (internalOfOddLabels PT hPT hm B ys)) :=
      (Lane_q_s15_c2.expect_map _ _ _).symm
    _ = _ := by rw [hMap]

theorem independent_label_singleton {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT) (b : OddPosition T k) (y : Fin (T.S.N k)) :
    (clusterIndependentLabelKernel PT hPT hm W B).pr
      (fun I => clusterLabelFromInternal (hPT := hPT) hm I b = y) = (oddLabelLaw PT hPT hm W B b).w y := by
  classical
  rw [Lane_sol_s15_transfer.pr_eq_E_indicator]
  let F : ClusterInternalData PT → ℝ := fun I =>
    @ite ℝ (clusterLabelFromInternal (hPT := hPT) hm I b = y) (Classical.propDecidable _) 1 0
  have hdep : ClusterLabelDependsOn hPT hm
      F {b} := by
    intro I I' hI
    dsimp only [F]
    rw [hI b (Finset.mem_singleton_self _)]
  change (clusterIndependentLabelKernel PT hPT hm W B).E F = _
  rw [independent_label_E_eq_odd_E PT hPT hm W B F {b} hdep]
  dsimp only [F]
  simp_rw [internalOfOddLabels_label]
  have h := Lane_sol_s15_transfer.E_pi_coord (oddLabelLaw PT hPT hm W B) b
    (fun z => @ite ℝ (z = y) (Classical.propDecidable _) 1 0)
  rw [h]
  simp [FinLaw.E]

end HypercubeRamsey.Lane_sol_s15_c2
