import HypercubeRamsey.S18.Nodes_sol_split_d18l_sol_d18l_cal_bounds
import HypercubeRamsey.S18.Nodes_sol_split_d18l_sol_d18l_cal_raw

namespace HypercubeRamsey.S18.Lane_sol_d18l_cal
open Classical
open scoped BigOperators
open S16 S16.Lane_sol_fix2_s16 S16.Lane_q_s16_comp2
set_option backward.isDefEq.respectTransparency false

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {G : LowGeom PT} {R : CellRawData G} {Perm : CellPermissions R}
  {K : CellRestrictedKernels R Perm} {S : CellCalibratedStages K}
  {F : FreshCell G} {Cal : FreshLabelCalibration F}

theorem calibration_history_weight (link : FreshConstructionLink S F Cal)
    (C : G.Cell) (W : Cal.Hist C) :
    (Cal.history C).w W = (R.history C).w (link.histories C W) := by
  rw [link.history_eq C, map_equiv_weight]
  rfl

theorem calibration_raw_support (link : FreshConstructionLink S F Cal)
    (C : G.Cell) (pool : F.Pool C) (ht : F.typical C pool) (W : Cal.Hist C)
    (hW : (Cal.gatedHistory C pool).w W ≠ 0) :
    (R.history C).w (link.histories C W) ≠ 0 ∧
      link.histories C W ∈ S.gate C pool := by
  rw [Cal.gated_eq C pool ht] at hW
  have h := S16.Lane_sol_s16_prod1.cond_support (Cal.history C) (Cal.gate C pool)
    (Cal.gate_pos C pool ht) W hW
  have hHist := h.2
  rw [link.history_eq C] at hHist
  obtain ⟨W', he, hw⟩ := map_support_exists (R.history C) (link.histories C).symm W hHist
  have he' : W' = link.histories C W := by
    simpa only [Equiv.apply_symm_apply] using congrArg (link.histories C) he
  constructor
  · rw [← he']; exact hw
  · have hg := h.1
    rw [link.gate_eq C pool] at hg
    obtain ⟨W', hgate, he⟩ := Finset.mem_image.mp hg
    have he' : W' = link.histories C W := by
      simpa only [Equiv.apply_symm_apply] using congrArg (link.histories C) he
    rw [← he']; exact hgate

/-- Transport the bin and label kernels back through their actual
construction equivalences, without replacing either probability law. -/
theorem calibration_stage_expect (link : FreshConstructionLink S F Cal)
    (C : G.Cell) (pool : F.Pool C) (W : Cal.Hist C)
    (f : (OddCellRole G C → Fin (T.S.N k)) → ℝ) :
    (Cal.binSampler C pool W).E (fun bins => (Cal.labelSampler C pool W bins).E f) =
      (S.binLaw C pool (link.histories C W)).E
        (fun bins => (S.labelLaw C pool (link.histories C W) bins).E f) := by
  classical
  rw [link.bin_eq C pool W, S16.Lane_q_s16_comp2.map_expect]
  apply congrArg
  funext bins
  rw [link.label_eq C pool W]
  simp only [Equiv.apply_symm_apply]

/-- Undo the own-cell history gate while retaining the typical-pool
premise. The remaining history is the product of the slice-conditioned laws. -/
theorem query_gate_bound (link : FreshConstructionLink S F Cal)
    (C : G.Cell) (pool : F.Pool C) (ht : F.typical C pool)
    (f : R.Hist C → ℝ) (hf : ∀ W, 0 ≤ f W) :
    (Cal.gatedHistory C pool).E (fun W => f (link.histories C W)) ≤
      (1 - Cal.δgate)⁻¹ * (R.history C).E f := by
  rw [Cal.gated_eq C pool ht]
  calc
    _ ≤ (1 - Cal.δgate)⁻¹ * (Cal.history C).E (fun W => f (link.histories C W)) :=
      cond_test_bound (Cal.history C) (Cal.gate C pool) (Cal.gate_pos C pool ht)
        Cal.δgate Cal.gate_range.2 (Cal.gate_mass C pool ht) _ (fun W => hf _)
    _ = _ := by
      rw [link.history_eq C, S16.Lane_q_s16_comp2.map_expect]
      simp only [Equiv.apply_symm_apply]

/-- The cluster bin comparison applies to every injectively indexed group
query family, with its original restricted target kernels. -/
theorem bin_query_comparison (C : G.Cell) (pool : F.Pool C) (W : R.Hist C)
    (ht : S.typical C pool) (hgate : W ∈ S.gate C pool)
    (hW : (R.history C).w W ≠ 0) (hc : PT.tiling.mode.isCluster)
    {q : ℕ} (g : Fin q → R.Group C) (hg : Function.Injective g)
    (b0 : Bin PT.tiling (G.cellPatch C))
    (f : (Fin q → Bin PT.tiling (G.cellPatch C)) → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (S.binLaw C pool W).E (fun bins => f (fun a => bins (g a))) ≤
      Real.exp (Real.rpow ((PT.tiling.P (G.cellPatch C)).d : ℝ) (-0.05) * q) *
        (FinLaw.pi fun a => K.qtilde C pool W (g a)).E f := by
  have hfeas := S.bin_feasible C pool W ht hgate hW hc
  have h := query_projection_upper (S.binLaw C pool W) (K.qtilde C pool W)
    g hg b0 (Real.rpow ((PT.tiling.P (G.cellPatch C)).d : ℝ) (-0.05))
    (fun bins => hfeas.2 (Finset.univ.image g) bins) f hf
  simpa only [Fintype.card_fin] using h

/-- The label comparison on a scope satisfying the actual per-bin query
allowance. The later repeat-mask step uses one retained role in each bin. -/
theorem cluster_label_cylinder (C : G.Cell) (pool : F.Pool C) (W : R.Hist C)
    (bins : R.Group C → Bin PT.tiling (G.cellPatch C))
    (ht : S.typical C pool) (hgate : W ∈ S.gate C pool)
    (hW : (R.history C).w W ≠ 0) (hb : (S.binLaw C pool W).w bins ≠ 0)
    (hc : PT.tiling.mode.isCluster) (scope : Finset (OddCellRole G C))
    (hscope : ∀ b, (scope.filter fun r => bins (R.groupOf C r) = b).card ≤
      (PT.tiling.P (G.cellPatch C)).h)
    (ys : OddCellRole G C → Fin (T.S.N k)) :
    (S.labelLaw C pool W bins).pr (fun x => ∀ r ∈ scope, x r = ys r) ≤
      Real.exp (Real.rpow ((PT.tiling.P (G.cellPatch C)).d : ℝ) (-0.01) * scope.card) *
        ∏ r ∈ scope, (R.U C W (R.groupOf C r) (bins (R.groupOf C r))).w (ys r) := by
  classical
  obtain ⟨L, hL⟩ := S.cluster_label_feasible C pool W bins ht hgate hW hb hc
  obtain ⟨e, hLabels, hBlocks⟩ := L.cluster_blocks hc
  have hQuery : L.problem.queries scope := by
    unfold RoleLabelProblem.queries
    rw [L.regime_eq, if_pos hc]
    intro b
    have hfilter : (scope.filter fun r => L.problem.blockOf r = b) =
        scope.filter (fun r => bins (R.groupOf C r) = e b) := by
      apply Finset.filter_congr
      intro r _
      rw [← hBlocks r]
      exact e.injective.eq_iff.symm
    rw [hfilter, L.height_eq]
    exact hscope (e b)
  have h := hL.2 scope ys hQuery
  simpa only [RoleLabelProblem.rate, L.regime_eq, L.scale_eq, L.targets_eq, if_pos hc] using h

theorem physical_cluster_restricted_cap (P : PhysicalFreshCertificate G F)
    (hc : PT.tiling.mode.isCluster) (C : G.Cell) (pool : F.Pool C) (ht : F.typical C pool)
    (W : P.raw.Hist C) (hW : (P.raw.history C).w W ≠ 0) (g : P.raw.Group C)
    (b : Bin PT.tiling (G.cellPatch C)) :
    (P.kernels.qtilde C pool W g).w b ≤
      if b ∈ Finset.univ.image pool then
        (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) * (8 * (PT.tiling.P (G.cellPatch C)).d) /
          G.nslot C else 0 := by
  let W' := (P.construction.histories C).symm W
  let g' := (P.construction.groups C).symm g
  have hW' : (P.calibration.history C).w W' ≠ 0 := by
    rw [calibration_history_weight P.construction]
    simpa only [W', Equiv.apply_symm_apply] using hW
  have hcap : ∀ b, (P.calibration.qin C W' g').w b ≤
      (8 * (PT.tiling.P (G.cellPatch C)).d) /
        Fintype.card (Bin PT.tiling (G.cellPatch C)) := by
    intro b
    rw [P.construction.incoming_eq]
    simpa only [W', g', Equiv.apply_symm_apply] using
      source_cluster_cap P.admissible P.quantitative P.raw P.source_valid P.scale hc C W hW g b
  have h := restricted_atom_cap P.calibration P.quantitative.n_large C pool ht W' hW' g'
    (8 * (PT.tiling.P (G.cellPatch C)).d) (by positivity) hcap b
  simpa only [P.construction.restricted_eq, W', g', Equiv.apply_symm_apply] using h

theorem physical_direct_restricted_cap (P : PhysicalFreshCertificate G F)
    (hc : ¬ PT.tiling.mode.isCluster) (C : G.Cell) (pool : F.Pool C) (ht : F.typical C pool)
    (W : P.raw.Hist C) (hW : (P.raw.history C).w W ≠ 0) (g : P.raw.Group C)
    (b : Bin PT.tiling (G.cellPatch C)) :
    (P.kernels.qtilde C pool W g).w b ≤
      if b ∈ Finset.univ.image pool then
        (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) / G.nslot C else 0 := by
  let W' := (P.construction.histories C).symm W
  let g' := (P.construction.groups C).symm g
  have hW' : (P.calibration.history C).w W' ≠ 0 := by
    rw [calibration_history_weight P.construction]
    simpa only [W', Equiv.apply_symm_apply] using hW
  have hcap : ∀ b, (P.calibration.qin C W' g').w b ≤
      (1 : ℝ) / Fintype.card (Bin PT.tiling (G.cellPatch C)) := by
    intro b
    rw [P.construction.incoming_eq]
    simpa only [W', g', Equiv.apply_symm_apply] using
      (source_direct_uniform P.raw P.source_valid hc C W hW g b).le
  have h := restricted_atom_cap P.calibration P.quantitative.n_large C pool ht W' hW' g'
    1 (by norm_num) hcap b
  simpa only [P.construction.restricted_eq, W', g', Equiv.apply_symm_apply, mul_one] using h

/-- Discard repeated-bin tests, then apply the label comparison to the
retained one-role-per-bin scope. -/
theorem cluster_label_tests (C : G.Cell) (pool : F.Pool C) (W : R.Hist C)
    (bins : R.Group C → Bin PT.tiling (G.cellPatch C))
    (ht : S.typical C pool) (hgate : W ∈ S.gate C pool)
    (hW : (R.history C).w W ≠ 0) (hb : (S.binLaw C pool W).w bins ≠ 0)
    (hc : PT.tiling.mode.isCluster) (hHeight : 1 ≤ (PT.tiling.P (G.cellPatch C)).h)
    {q : ℕ} (r : Fin q → OddCellRole G C) (hr : Function.Injective r)
    (f : Fin q → Fin (T.S.N k) → ℝ) (hf : ∀ a y, 0 ≤ f a y ∧ f a y ≤ 1) :
    (S.labelLaw C pool W bins).E (fun ys => ∏ a, f a (ys (r a))) ≤
      Real.exp (Real.rpow ((PT.tiling.P (G.cellPatch C)).d : ℝ) (-0.01) * q) *
        retainedQueryWeight (fun a b => (R.U C W (R.groupOf C (r a)) b).E (f a))
          (fun a => bins (R.groupOf C (r a))) := by
  classical
  let xs := fun a => bins (R.groupOf C (r a))
  let J := queryRepeatMask xs
  let K := Finset.univ.filter fun a => J a = false
  let u := fun a b => (R.U C W (R.groupOf C (r a)) b).E (f a)
  let rate := Real.rpow ((PT.tiling.P (G.cellPatch C)).d : ℝ) (-0.01)
  have hdrop (ys : OddCellRole G C → Fin (T.S.N k)) :
      (∏ a, f a (ys (r a))) ≤ ∏ a ∈ K, f a (ys (r a)) := by
    rw [← product_kept J]
    apply Finset.prod_le_prod₀
    · intro a _; exact (hf a _).1
    · intro a _
      split_ifs
      · exact (hf a _).2
      · exact le_rfl
  have hLabel := indexed_scope_test_bound (S.labelLaw C pool W bins)
    (fun v => R.U C W (R.groupOf C v) (bins (R.groupOf C v))) K r hr
    (⟨0, T.S.N_pos k⟩ : Fin (T.S.N k)) rate
    (fun ys => cluster_label_cylinder C pool W bins ht hgate hW hb hc (K.image r)
      (fun b => (retained_role_bin_count r (R.groupOf C) bins b).trans hHeight) ys)
    f (fun a y => (hf a y).1)
  have hcard : K.card ≤ q := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
  have hr0 : 0 ≤ rate := by dsimp [rate]; positivity
  have hcost : Real.exp (rate * K.card) ≤ Real.exp (rate * q) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hr0)
  have hprod : 0 ≤ ∏ a ∈ K, u a (xs a) := Finset.prod_nonneg (fun a _ =>
    expect_nonneg _ _ (fun y => (hf a y).1))
  have hidentity : (∏ a ∈ K, u a (xs a)) = retainedQueryWeight u xs := by
    rw [retained_weight_product, product_kept]
  calc
    _ ≤ (S.labelLaw C pool W bins).E (fun ys => ∏ a ∈ K, f a (ys (r a))) :=
      expect_le _ _ _ hdrop
    _ ≤ Real.exp (rate * K.card) * ∏ a ∈ K, u a (xs a) := hLabel
    _ ≤ Real.exp (rate * q) * ∏ a ∈ K, u a (xs a) :=
      mul_le_mul_of_nonneg_right hcost hprod
    _ = _ := by rw [hidentity]

/-- Conditional two-stage test comparison on distinct queried groups. -/
theorem cluster_conditional_tests (C : G.Cell) (pool : F.Pool C) (W : R.Hist C)
    (ht : S.typical C pool) (hgate : W ∈ S.gate C pool)
    (hW : (R.history C).w W ≠ 0) (hc : PT.tiling.mode.isCluster)
    (hHeight : 1 ≤ (PT.tiling.P (G.cellPatch C)).h)
    {q : ℕ} (r : Fin q → OddCellRole G C) (hr : Function.Injective r)
    (hg : Function.Injective (fun a => R.groupOf C (r a)))
    (b0 : Bin PT.tiling (G.cellPatch C))
    (f : Fin q → Fin (T.S.N k) → ℝ) (hf : ∀ a y, 0 ≤ f a y ∧ f a y ≤ 1) :
    (S.binLaw C pool W).E (fun bins =>
      (S.labelLaw C pool W bins).E (fun ys => ∏ a, f a (ys (r a)))) ≤
      Real.exp ((Real.rpow ((PT.tiling.P (G.cellPatch C)).d : ℝ) (-0.05) +
        Real.rpow ((PT.tiling.P (G.cellPatch C)).d : ℝ) (-0.01)) * q) *
        (FinLaw.pi fun a => K.qtilde C pool W (R.groupOf C (r a))).E
          (retainedQueryWeight (fun a b => (R.U C W (R.groupOf C (r a)) b).E (f a))) := by
  let u := fun a b => (R.U C W (R.groupOf C (r a)) b).E (f a)
  let rateB := Real.rpow ((PT.tiling.P (G.cellPatch C)).d : ℝ) (-0.05)
  let rateL := Real.rpow ((PT.tiling.P (G.cellPatch C)).d : ℝ) (-0.01)
  have hu : ∀ a b, 0 ≤ u a b := fun a b => expect_nonneg _ _ (fun y => (hf a y).1)
  calc
    _ ≤ (S.binLaw C pool W).E (fun bins => Real.exp (rateL * q) *
        retainedQueryWeight u (fun a => bins (R.groupOf C (r a)))) := by
      apply expect_le_on_support
      intro bins hb
      exact cluster_label_tests C pool W bins ht hgate hW hb hc hHeight r hr f hf
    _ = Real.exp (rateL * q) * (S.binLaw C pool W).E
        (fun bins => retainedQueryWeight u (fun a => bins (R.groupOf C (r a)))) := expect_const_mul _ _ _
    _ ≤ Real.exp (rateL * q) * (Real.exp (rateB * q) *
        (FinLaw.pi fun a => K.qtilde C pool W (R.groupOf C (r a))).E (retainedQueryWeight u)) :=
      mul_le_mul_of_nonneg_left
        (bin_query_comparison C pool W ht hgate hW hc (fun a => R.groupOf C (r a)) hg b0
          (retainedQueryWeight u) (retainedQueryWeight_nonneg u hu)) (Real.exp_pos _).le
    _ = _ := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem physical_restricted_relative_cap (P : PhysicalFreshCertificate G F)
    (C : G.Cell) (pool : F.Pool C) (ht : F.typical C pool)
    (W : P.raw.Hist C) (hW : (P.raw.history C).w W ≠ 0) (g : P.raw.Group C)
    (b : Bin PT.tiling (G.cellPatch C)) :
    (P.kernels.qtilde C pool W g).w b ≤
      if b ∈ Finset.univ.image pool then
        ((1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) * (1 - (0.00001 : ℝ))⁻¹ *
          Fintype.card (Bin PT.tiling (G.cellPatch C)) / G.nslot C) *
            (P.raw.qraw C W g).w b else 0 := by
  classical
  let W' := (P.construction.histories C).symm W
  let g' := (P.construction.groups C).symm g
  let B : ℝ := Fintype.card (Bin PT.tiling (G.cellPatch C))
  let A := B * (1 - (0.00001 : ℝ))⁻¹ * (P.raw.qraw C W g).w b
  have hB : 0 < B := by
    letI := nonempty_of_finLaw (P.calibration.qin C W' g')
    dsimp [B]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Bin PT.tiling (G.cellPatch C)))
  have hW' : (P.calibration.history C).w W' ≠ 0 := by
    rw [calibration_history_weight P.construction]
    simpa only [W', Equiv.apply_symm_apply] using hW
  have hcap : (P.calibration.qin C W' g').w b ≤ A / B := by
    rw [P.construction.incoming_eq]
    have h := source_pretrim_relative_cap P.admissible P.quantitative.profiled_valid
      P.raw P.source_valid C W hW g b
    have he : A / B = (1 - (0.00001 : ℝ))⁻¹ * (P.raw.qraw C W g).w b := by
      dsimp [A]
      field_simp
    simpa only [W', g', Equiv.apply_symm_apply, he] using h
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (by positivity) ((P.raw.qraw C W g).nonneg b)
  have h := restricted_atom_bound P.calibration P.quantitative.n_large C pool ht W' hW' g' A hA b hcap
  have he : (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) * A / G.nslot C =
      ((1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) * (1 - (0.00001 : ℝ))⁻¹ * B / G.nslot C) *
        (P.raw.qraw C W g).w b := by dsimp [A]; ring
  simpa only [P.construction.restricted_eq, W', g', Equiv.apply_symm_apply, he] using h

noncomputable def mixed_query_law (C : G.Cell) (pool : F.Pool C) (W : R.Hist C)
    (r : OddCellRole G C) : FinLaw (Fin (T.S.N k)) where
  w := fun y => ∑ b, (K.qtilde C pool W (R.groupOf C r)).w b * (R.U C W (R.groupOf C r) b).w y
  nonneg := fun y => Finset.sum_nonneg (fun b _ =>
    mul_nonneg ((K.qtilde C pool W _).nonneg b) ((R.U C W _ b).nonneg y))
  sum_one := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, FinLaw.sum_one, mul_one]
    exact (K.qtilde C pool W _).sum_one

theorem mixed_query_expect (C : G.Cell) (pool : F.Pool C) (W : R.Hist C)
    (r : OddCellRole G C) (f : Fin (T.S.N k) → ℝ) :
    (mixed_query_law (K := K) (F := F) C pool W r).E f =
      (K.qtilde C pool W (R.groupOf C r)).E (fun b => (R.U C W (R.groupOf C r) b).E f) := by
  unfold FinLaw.E mixed_query_law
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Direct-mode comparison of all queried labels, followed by the same
repeat-mask weakening used for the cluster bin calculation. -/
theorem direct_conditional_tests (C : G.Cell) (pool : F.Pool C) (W : R.Hist C)
    (ht : S.typical C pool) (hgate : W ∈ S.gate C pool)
    (hW : (R.history C).w W ≠ 0) (hc : ¬ PT.tiling.mode.isCluster)
    {q : ℕ} (r : Fin q → OddCellRole G C) (hr : Function.Injective r)
    (hSmall : (q : ℝ) ≤ Real.rpow (G.nslot C : ℝ) 0.025)
    (f : Fin q → Fin (T.S.N k) → ℝ) (hf : ∀ a y, 0 ≤ f a y ∧ f a y ≤ 1) :
    (S.binLaw C pool W).E (fun bins =>
      (S.labelLaw C pool W bins).E (fun ys => ∏ a, f a (ys (r a)))) ≤
      Real.exp (Real.rpow (G.nslot C : ℝ) (-0.04) * q) *
        (FinLaw.pi fun a => K.qtilde C pool W (R.groupOf C (r a))).E
          (retainedQueryWeight (fun a b => (R.U C W (R.groupOf C (r a)) b).E (f a))) := by
  classical
  let Q := FinLaw.bind (S.binLaw C pool W) (S.labelLaw C pool W)
  let L := FinLaw.map Q Prod.snd
  let rate := Real.rpow (G.nslot C : ℝ) (-0.04)
  let u := fun a b => (R.U C W (R.groupOf C (r a)) b).E (f a)
  have hcard : ((Finset.univ : Finset (Fin q)).image r).card = q := by
    rw [Finset.card_image_of_injective _ hr]
    simp
  have hCyl (ys : OddCellRole G C → Fin (T.S.N k)) :
      L.pr (fun x => ∀ v ∈ Finset.univ.image r, x v = ys v) ≤
        Real.exp (rate * (Finset.univ.image r).card) *
          ∏ v ∈ Finset.univ.image r, (mixed_query_law (K := K) (F := F) C pool W v).w (ys v) := by
    rw [map_pr]
    exact S.direct_joint C pool W (Finset.univ.image r) ys ht hgate hW hc (by simpa [hcard] using hSmall)
  have hLabel := indexed_scope_test_bound L
    (mixed_query_law (K := K) (F := F) C pool W) Finset.univ r hr
    (⟨0, T.S.N_pos k⟩ : Fin (T.S.N k)) rate hCyl f (fun a y => (hf a y).1)
  have hEq : L.E (fun ys => ∏ a, f a (ys (r a))) =
      (S.binLaw C pool W).E (fun bins =>
        (S.labelLaw C pool W bins).E (fun ys => ∏ a, f a (ys (r a)))) := by
    rw [S16.Lane_q_s16_comp2.map_expect, bind_expect]
  rw [hEq] at hLabel
  have hu0 : ∀ a b, 0 ≤ u a b := fun a b => expect_nonneg _ _ (fun y => (hf a y).1)
  have hu1 : ∀ a b, u a b ≤ 1 := by
    intro a b
    calc
      _ ≤ (R.U C W (R.groupOf C (r a)) b).E (fun _ => 1) :=
        expect_le _ _ _ (fun y => (hf a y).2)
      _ = 1 := expect_const _ _
  calc
    _ ≤ Real.exp (rate * q) * ∏ a, (mixed_query_law (K := K) (F := F) C pool W (r a)).E (f a) := by
      simpa only [Finset.card_univ, Fintype.card_fin] using hLabel
    _ = Real.exp (rate * q) * (FinLaw.pi fun a => K.qtilde C pool W (R.groupOf C (r a))).E
        (fun xs => ∏ a, u a (xs a)) := by
      simp_rw [mixed_query_expect]
      rw [S16.Lane_q_s16_comp2.pi_expect_prod]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply expect_le
      intro xs
      rw [retained_weight_product]
      apply Finset.prod_le_prod₀
      · intro a _; exact hu0 _ _
      · intro a _; split_ifs
        · exact hu1 _ _
        · exact le_rfl

/-- In direct modes both raw kernels are fixed uniform/singleton readouts,
so every raw query moment already equals its prescribed profile mean. -/
theorem physical_direct_raw_moment (P : PhysicalFreshCertificate G F)
    (hc : ¬ PT.tiling.mode.isCluster) (C : G.Cell) (r : OddCellRole G C)
    (W : P.raw.Hist C) (f : Fin (T.S.N k) → ℝ) :
    rawQueryMoment P.raw C r W f = ∑ y, (PT.πraw (G.cellPatch C)).w y * f y := by
  classical
  obtain ⟨hc', hSource⟩ := P.source_valid.resolve_left (fun h => hc (by simp [h.1, Mode.isCluster]))
  have hQ := (hSource C).2.2.2.1
  have hU := (hSource C).2.2.2.2.2.1
  let B : ℝ := Fintype.card (Bin PT.tiling (G.cellPatch C))
  let mean := fun y => ∑ b : Bin PT.tiling (G.cellPatch C), (1 / B) * (if y ∈ b.1 then 1 else 0)
  have hIncoming (W' : P.calibration.Hist C) (hW' : (P.calibration.history C).w W' ≠ 0)
      (g : P.calibration.Group C) (b : Bin PT.tiling (G.cellPatch C)) :
      (P.calibration.qin C W' g).w b = 1 / B := by
    rw [P.construction.incoming_eq]
    have hrW : (P.raw.history C).w (P.construction.histories C W') ≠ 0 := by
      rwa [calibration_history_weight P.construction] at hW'
    exact source_direct_uniform P.raw P.source_valid hc C _ hrW _ b
  have hMean (y : Fin (T.S.N k)) : mean y = (PT.π (G.cellPatch C)).w y := by
    have hm : (P.calibration.history C).E (fun W' =>
        ∑ b, (P.calibration.qin C W' (P.calibration.groupOf C r)).w b *
          (P.calibration.U C W' (P.calibration.groupOf C r) b).w y) = mean y := by
      calc
        _ = (P.calibration.history C).E (fun _ => mean y) := by
          apply expect_congr_of_support
          intro W' hW'
          apply Finset.sum_congr rfl
          intro b _
          rw [hIncoming W' hW', P.construction.U_eq, hU]
        _ = _ := expect_const _ _
    exact hm.symm.trans (P.calibration.raw_profile C r y)
  unfold rawQueryMoment
  simp_rw [hQ, hU, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ y, mean y * f y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      rw [hMean, P.quantitative.profiled_valid.raw_direct hc]

theorem physical_conditioned_queries (P : PhysicalFreshCertificate G F)
    (C : G.Cell) {A : Type*} [Fintype A] [DecidableEq A]
    (r : A → OddCellRole G C) (f : A → Fin (T.S.N k) → ℝ) (hf : ∀ a y, 0 ≤ f a y)
    (hMargin : PT.tiling.mode.isCluster → 2 < 20 * κ.ρ * (PT.tiling.P (G.cellPatch C)).h)
    (hSep : ∀ a b, a ≠ b → 50 * κ.ρ * (PT.tiling.P (G.cellPatch C)).h <
      (hammingDist (r a).1 (r b).1 : ℝ)) :
    (P.raw.history C).E (fun W => ∏ a, rawQueryMoment P.raw C (r a) W (f a)) ≤
      (1 - (0.00001 : ℝ))⁻¹ ^ Fintype.card A *
        ∏ a, ∑ y, (PT.πraw (G.cellPatch C)).w y * f a y := by
  classical
  by_cases hc : PT.tiling.mode.isCluster
  · exact source_cluster_conditioned_queries P.admissible P.quantitative.profiled_valid
      P.raw P.source_valid hc C r f hf (hMargin hc) hSep
  · simp_rw [physical_direct_raw_moment P hc]
    rw [expect_const]
    apply le_mul_of_one_le_left
    · exact Finset.prod_nonneg (fun a _ => Finset.sum_nonneg (fun y _ =>
        mul_nonneg ((PT.πraw _).nonneg y) (hf a y)))
    · exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ (1 - (0.00001 : ℝ))⁻¹)

noncomputable def cell_query_rate (G : LowGeom PT) (C : G.Cell) : ℝ :=
  if PT.tiling.mode.isCluster then
    Real.rpow ((PT.tiling.P (G.cellPatch C)).d : ℝ) (-0.05) +
      Real.rpow ((PT.tiling.P (G.cellPatch C)).d : ℝ) (-0.01)
  else Real.rpow (G.nslot C : ℝ) (-0.04)

theorem physical_fresh_query_comparison (P : PhysicalFreshCertificate G F)
    (C : G.Cell) (pool : F.Pool C) (ht : F.typical C pool)
    {q : ℕ} (r : Fin q → OddCellRole G C) (hr : Function.Injective r)
    (hg : Function.Injective (fun a => P.raw.groupOf C (r a)))
    (hHeight : PT.tiling.mode.isCluster → 1 ≤ (PT.tiling.P (G.cellPatch C)).h)
    (hSmall : ¬ PT.tiling.mode.isCluster → (q : ℝ) ≤ Real.rpow (G.nslot C : ℝ) 0.025)
    (b0 : Bin PT.tiling (G.cellPatch C))
    (f : Fin q → Fin (T.S.N k) → ℝ) (hf : ∀ a y, 0 ≤ f a y ∧ f a y ≤ 1) :
    (F.fresh C pool).E (fun s => ∏ a, f a (F.label C s (r a).1)) ≤
      (Real.exp (cell_query_rate G C * q) * (1 + (T.S.n k : ℝ) ^ (-3 : ℝ))) *
        (P.raw.history C).E (fun W =>
          (FinLaw.pi fun a => P.kernels.qtilde C pool W (P.raw.groupOf C (r a))).E
            (retainedQueryWeight (fun a b => (P.raw.U C W (P.raw.groupOf C (r a)) b).E (f a)))) := by
  classical
  let Φ := fun W : P.raw.Hist C =>
    (FinLaw.pi fun a => P.kernels.qtilde C pool W (P.raw.groupOf C (r a))).E
      (retainedQueryWeight (fun a b => (P.raw.U C W (P.raw.groupOf C (r a)) b).E (f a)))
  have hΦ : ∀ W, 0 ≤ Φ W := by
    intro W
    apply expect_nonneg
    apply retainedQueryWeight_nonneg
    intro a b
    exact expect_nonneg _ _ (fun y => (hf a y).1)
  have htyp := (P.construction.typical_eq C pool).mp ht
  have hStage (W : P.calibration.Hist C) (hW : (P.calibration.gatedHistory C pool).w W ≠ 0) :
      (P.calibration.binSampler C pool W).E (fun bins =>
        (P.calibration.labelSampler C pool W bins).E (fun ys => ∏ a, f a (ys (r a)))) ≤
        Real.exp (cell_query_rate G C * q) * Φ (P.construction.histories C W) := by
    obtain ⟨hHist, hGate⟩ := calibration_raw_support P.construction C pool ht W hW
    rw [calibration_stage_expect P.construction C pool W]
    by_cases hc : PT.tiling.mode.isCluster
    · simpa only [cell_query_rate, if_pos hc] using
        cluster_conditional_tests C pool _ htyp hGate hHist hc (hHeight hc) r hr hg b0 f hf
    · simpa only [cell_query_rate, if_neg hc] using
        direct_conditional_tests C pool _ htyp hGate hHist hc r hr (hSmall hc) f hf
  rw [query_stage_readout P.calibration C pool ht r f]
  calc
    _ ≤ (P.calibration.gatedHistory C pool).E (fun W =>
        Real.exp (cell_query_rate G C * q) * Φ (P.construction.histories C W)) :=
      expect_le_on_support _ _ _ hStage
    _ = Real.exp (cell_query_rate G C * q) *
        (P.calibration.gatedHistory C pool).E (fun W => Φ (P.construction.histories C W)) := expect_const_mul _ _ _
    _ ≤ Real.exp (cell_query_rate G C * q) * ((1 - P.calibration.δgate)⁻¹ * (P.raw.history C).E Φ) :=
      mul_le_mul_of_nonneg_left (query_gate_bound P.construction C pool ht Φ hΦ) (Real.exp_pos _).le
    _ ≤ Real.exp (cell_query_rate G C * q) *
        ((1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) * (P.raw.history C).E Φ) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_right (calibration_gate_price P.calibration P.quantitative.n_large)
        (expect_nonneg _ _ hΦ)
    _ = _ := by ring

theorem physical_masked_records_bound (P : PhysicalFreshCertificate G F) (C : G.Cell)
    {q : ℕ} (J : Fin q → Bool) (r : Fin q → OddCellRole G C)
    (f : Fin q → Fin (T.S.N k) → ℝ) (hf : ∀ a y, 0 ≤ f a y)
    (hMargin : PT.tiling.mode.isCluster → 2 < 20 * κ.ρ * (PT.tiling.P (G.cellPatch C)).h)
    (hSep : ∀ a b, a ≠ b → 50 * κ.ρ * (PT.tiling.P (G.cellPatch C)).h <
      (hammingDist (r a).1 (r b).1 : ℝ)) :
    (P.raw.history C).E (fun W =>
      (FinLaw.pi fun a => P.raw.qraw C W (P.raw.groupOf C (r a))).E
        (keptMaskWeight J (fun a b => (P.raw.U C W (P.raw.groupOf C (r a)) b).E (f a)) ∅)) ≤
      (1 - (0.00001 : ℝ))⁻¹ ^ q *
        ∏ a, if J a then 1 else ∑ y, (PT.πraw (G.cellPatch C)).w y * f a y := by
  classical
  let K := Finset.univ.filter fun a => J a = false
  let A := {a : Fin q // a ∈ K}
  have hcell := physical_conditioned_queries P C (fun a : A => r a.1) (fun a => f a.1)
    (fun a y => hf a.1 y) hMargin
    (fun a b hab => hSep a.1 b.1 (fun he => hab (Subtype.ext he)))
  have hprod (W : P.raw.Hist C) : (∏ a ∈ K, rawQueryMoment P.raw C (r a) W (f a)) =
      ∏ a : A, rawQueryMoment P.raw C (r a.1) W (f a.1) :=
    Finset.prod_subtype K (fun _ => Iff.rfl) _
  have hprod' : (∏ a ∈ K, ∑ y, (PT.πraw (G.cellPatch C)).w y * f a y) =
      ∏ a : A, ∑ y, (PT.πraw (G.cellPatch C)).w y * f a.1 y :=
    Finset.prod_subtype K (fun _ => Iff.rfl) _
  have hcard : Fintype.card A ≤ q := by
    calc
      Fintype.card A = K.card := Fintype.card_coe K
      _ ≤ q := (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
  have hcost : (1 - (0.00001 : ℝ))⁻¹ ^ Fintype.card A ≤
      (1 - (0.00001 : ℝ))⁻¹ ^ q := pow_le_pow_right₀ (by norm_num) hcard
  have hnonneg : 0 ≤ ∏ a : A, ∑ y, (PT.πraw (G.cellPatch C)).w y * f a.1 y :=
    Finset.prod_nonneg (fun a _ => Finset.sum_nonneg (fun y _ =>
      mul_nonneg ((PT.πraw _).nonneg y) (hf a.1 y)))
  calc
    _ ≤ (P.raw.history C).E (fun W => ∏ a ∈ K, rawQueryMoment P.raw C (r a) W (f a)) := by
      apply expect_le
      intro W
      have h := kept_expect_product_le
        (fun a => P.raw.qraw C W (P.raw.groupOf C (r a))) J
        (fun a b => (P.raw.U C W (P.raw.groupOf C (r a)) b).E (f a))
        (fun a b => expect_nonneg _ _ (hf a))
      rw [product_kept] at h
      exact h
    _ ≤ (1 - (0.00001 : ℝ))⁻¹ ^ Fintype.card A *
        ∏ a : A, ∑ y, (PT.πraw (G.cellPatch C)).w y * f a.1 y := by
      simp_rw [hprod]
      exact hcell
    _ ≤ (1 - (0.00001 : ℝ))⁻¹ ^ q *
        ∏ a : A, ∑ y, (PT.πraw (G.cellPatch C)).w y * f a.1 y :=
      mul_le_mul_of_nonneg_right hcost hnonneg
    _ = _ := by rw [← hprod', product_kept]

theorem physical_restricted_cap (P : PhysicalFreshCertificate G F)
    (C : G.Cell) (pool : F.Pool C) (ht : F.typical C pool)
    (W : P.raw.Hist C) (hW : (P.raw.history C).w W ≠ 0) (g : P.raw.Group C)
    (b : Bin PT.tiling (G.cellPatch C)) :
    (P.kernels.qtilde C pool W g).w b ≤
      if b ∈ Finset.univ.image pool then
        (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) * (8 * (PT.tiling.P (G.cellPatch C)).d) / G.nslot C else 0 := by
  by_cases hc : PT.tiling.mode.isCluster
  · exact physical_cluster_restricted_cap P hc C pool ht W hW g b
  · have h := physical_direct_restricted_cap P hc C pool ht W hW g b
    have hd := source_direct_bin_size P.admissible P.quantitative hc (G.cellPatch C)
    rw [hd]
    by_cases hb : b ∈ Finset.univ.image pool
    · simp only [if_pos hb] at h ⊢
      apply h.trans
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      have he : 0 ≤ 1 + (T.S.n k : ℝ) ^ (-3 : ℝ) := by positivity
      simpa only [Nat.cast_one, mul_one] using
        mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) ≤ 8) he
    · simpa only [if_neg hb] using h

theorem physical_pool_mask_bound (P : PhysicalFreshCertificate G F) (C : G.Cell)
    (hBins : (Finset.univ : Finset (Bin PT.tiling (G.cellPatch C))).Nonempty)
    {q : ℕ} (J : Fin q → Bool) (r : Fin q → OddCellRole G C)
    (W : P.raw.Hist C) (hW : (P.raw.history C).w W ≠ 0)
    (f : Fin q → Fin (T.S.N k) → ℝ) (hf : ∀ a y, 0 ≤ f a y)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hallow : (q : ℝ) * ((1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) *
      (8 * (PT.tiling.P (G.cellPatch C)).d) / G.nslot C) ≤ δ) :
    (S16.iidCellPoolLaw (G := G) C hBins).E (fun pool => if F.typical C pool then
      (FinLaw.pi fun a => P.kernels.qtilde C pool W (P.raw.groupOf C (r a))).E
        (repeatMaskWeight J (fun a b => (P.raw.U C W (P.raw.groupOf C (r a)) b).E (f a)) ∅)
      else 0) ≤
      δ ^ maskDrops J * ((1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) * (1 - (0.00001 : ℝ))⁻¹) ^ q *
        (FinLaw.pi fun a => P.raw.qraw C W (P.raw.groupOf C (r a))).E
          (keptMaskWeight J (fun a b => (P.raw.U C W (P.raw.groupOf C (r a)) b).E (f a)) ∅) := by
  classical
  let A := (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) * (8 * (PT.tiling.P (G.cellPatch C)).d) / G.nslot C
  let c := (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) * (1 - (0.00001 : ℝ))⁻¹
  let Q := fun a => P.raw.qraw C W (P.raw.groupOf C (r a))
  let u := fun a b => (P.raw.U C W (P.raw.groupOf C (r a)) b).E (f a)
  let PoolLaw := S16.iidCellPoolLaw (G := G) C hBins
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : 1 ≤ c := by
    dsimp [c]
    calc
      (1 : ℝ) ≤ (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) * 1 := by
        have he : 0 ≤ (T.S.n k : ℝ) ^ (-3 : ℝ) := by positivity
        simpa only [mul_one] using (show (1 : ℝ) ≤ 1 + (T.S.n k : ℝ) ^ (-3 : ℝ) by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by norm_num)
        (show (0 : ℝ) ≤ 1 + (T.S.n k : ℝ) ^ (-3 : ℝ) by positivity)
  have hu : ∀ a b, 0 ≤ u a b := fun a b => expect_nonneg _ _ (hf a)
  have hpoint (pool : F.Pool C) :
      (if F.typical C pool then
        (FinLaw.pi fun a => P.kernels.qtilde C pool W (P.raw.groupOf C (r a))).E
          (repeatMaskWeight J u ∅) else 0) ≤
      (q * A) ^ maskDrops J * (if F.typical C pool then
        (FinLaw.pi fun a => P.kernels.qtilde C pool W (P.raw.groupOf C (r a))).E
          (keptMaskWeight J u ∅) else 0) := by
    by_cases ht : F.typical C pool
    · rw [if_pos ht, if_pos ht]
      have hcap : ∀ a b, (P.kernels.qtilde C pool W (P.raw.groupOf C (r a))).w b ≤ A := by
        intro a b
        have h := physical_restricted_cap P C pool ht W hW (P.raw.groupOf C (r a)) b
        by_cases hb : b ∈ Finset.univ.image pool
        · simpa only [if_pos hb] using h
        · simp only [if_neg hb] at h
          exact h.trans hA
      exact reverse_masks q A hA q le_rfl _ hcap J u hu ∅
    · simp [ht]
  have hKept := kept_typical_pool_comparison C hBins (P.calibration.slot_pos C) J Q
    (fun pool a => P.kernels.qtilde C pool W (P.raw.groupOf C (r a))) (F.typical C) c hc
    (fun pool ht a b => by simpa only [mul_div_assoc] using
      physical_restricted_relative_cap P C pool ht W hW (P.raw.groupOf C (r a)) b)
    u hu
  have hcost : c ^ (q - maskDrops J) ≤ c ^ q := pow_le_pow_right₀ hc1 (Nat.sub_le _ _)
  have hprice : (q * A) ^ maskDrops J ≤ δ ^ maskDrops J :=
    pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hA) hallow _
  have hRaw0 : 0 ≤ (FinLaw.pi Q).E (keptMaskWeight J u ∅) :=
    expect_nonneg _ _ (keptMaskWeight_nonneg J u hu ∅)
  calc
    _ ≤ PoolLaw.E (fun pool => (q * A) ^ maskDrops J *
        (if F.typical C pool then
          (FinLaw.pi fun a => P.kernels.qtilde C pool W (P.raw.groupOf C (r a))).E
            (keptMaskWeight J u ∅) else 0)) := expect_le _ _ _ hpoint
    _ = (q * A) ^ maskDrops J * PoolLaw.E (fun pool => if F.typical C pool then
        (FinLaw.pi fun a => P.kernels.qtilde C pool W (P.raw.groupOf C (r a))).E
          (keptMaskWeight J u ∅) else 0) := expect_const_mul _ _ _
    _ ≤ (q * A) ^ maskDrops J * (c ^ (q - maskDrops J) * (FinLaw.pi Q).E (keptMaskWeight J u ∅)) :=
      mul_le_mul_of_nonneg_left hKept (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hA) _)
    _ ≤ δ ^ maskDrops J * (c ^ q * (FinLaw.pi Q).E (keptMaskWeight J u ∅)) := by
      apply mul_le_mul hprice (mul_le_mul_of_nonneg_right hcost hRaw0)
      · exact mul_nonneg (pow_nonneg hc _) hRaw0
      · exact pow_nonneg hδ _
    _ = _ := by ring

theorem physical_pool_record_bound (P : PhysicalFreshCertificate G F) (C : G.Cell)
    (hBins : (Finset.univ : Finset (Bin PT.tiling (G.cellPatch C))).Nonempty)
    {q : ℕ} (r : Fin q → OddCellRole G C)
    (f : Fin q → Fin (T.S.N k) → ℝ) (hf : ∀ a y, 0 ≤ f a y)
    (hMargin : PT.tiling.mode.isCluster → 2 < 20 * κ.ρ * (PT.tiling.P (G.cellPatch C)).h)
    (hSep : ∀ a b, a ≠ b → 50 * κ.ρ * (PT.tiling.P (G.cellPatch C)).h <
      (hammingDist (r a).1 (r b).1 : ℝ))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hallow : (q : ℝ) * ((1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) *
      (8 * (PT.tiling.P (G.cellPatch C)).d) / G.nslot C) ≤ δ) :
    (S16.iidCellPoolLaw (G := G) C hBins).E (fun pool => if F.typical C pool then
      (P.raw.history C).E (fun W =>
        (FinLaw.pi fun a => P.kernels.qtilde C pool W (P.raw.groupOf C (r a))).E
          (retainedQueryWeight (fun a b => (P.raw.U C W (P.raw.groupOf C (r a)) b).E (f a)))) else 0) ≤
      ((1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) * (1 - (0.00001 : ℝ))⁻¹) ^ q *
        (1 - (0.00001 : ℝ))⁻¹ ^ q *
          ∏ a, ((∑ y, (PT.πraw (G.cellPatch C)).w y * f a y) + δ) := by
  classical
  let PoolLaw := S16.iidCellPoolLaw (G := G) C hBins
  let H := P.raw.history C
  let c := (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) * (1 - (0.00001 : ℝ))⁻¹
  let s := (1 - (0.00001 : ℝ))⁻¹
  let μ := fun a => ∑ y, (PT.πraw (G.cellPatch C)).w y * f a y
  let u := fun (W : P.raw.Hist C) a b => (P.raw.U C W (P.raw.groupOf C (r a)) b).E (f a)
  let Qt := fun pool W a => P.kernels.qtilde C pool W (P.raw.groupOf C (r a))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hs : 0 ≤ s := by dsimp [s]; norm_num
  have hu : ∀ W a b, 0 ≤ u W a b := fun W a b => expect_nonneg _ _ (hf a)
  have hJ (J : Fin q → Bool) :
      H.E (fun W => PoolLaw.E (fun pool => if F.typical C pool then
        (FinLaw.pi (Qt pool W)).E (repeatMaskWeight J (u W) ∅) else 0)) ≤
        (c ^ q * s ^ q) * (δ ^ maskDrops J * ∏ a, if J a then 1 else μ a) := by
    have hMask := physical_masked_records_bound P C J r f hf hMargin hSep
    calc
      _ ≤ H.E (fun W => (δ ^ maskDrops J * c ^ q) *
          (FinLaw.pi fun a => P.raw.qraw C W (P.raw.groupOf C (r a))).E
            (keptMaskWeight J (u W) ∅)) := by
        apply expect_le_on_support
        intro W hW
        exact physical_pool_mask_bound P C hBins J r W hW f hf δ hδ hallow
      _ = (δ ^ maskDrops J * c ^ q) * H.E (fun W =>
          (FinLaw.pi fun a => P.raw.qraw C W (P.raw.groupOf C (r a))).E
            (keptMaskWeight J (u W) ∅)) := expect_const_mul _ _ _
      _ ≤ (δ ^ maskDrops J * c ^ q) * (s ^ q * ∏ a, if J a then 1 else μ a) :=
        mul_le_mul_of_nonneg_left hMask (mul_nonneg (pow_nonneg hδ _) (pow_nonneg hc _))
      _ = _ := by ring
  calc
    _ = H.E (fun W => PoolLaw.E (fun pool => if F.typical C pool then
        (FinLaw.pi (Qt pool W)).E (retainedQueryWeight (u W)) else 0)) := by
      calc
        _ = PoolLaw.E (fun pool => H.E (fun W => if F.typical C pool then
            (FinLaw.pi (Qt pool W)).E (retainedQueryWeight (u W)) else 0)) := by
          apply congrArg
          funext pool
          exact (expect_if_const H (F.typical C pool) _).symm
        _ = _ := expect_indep_comm _ _ _
    _ ≤ H.E (fun W => PoolLaw.E (fun pool => ∑ J : Fin q → Bool,
        if F.typical C pool then (FinLaw.pi (Qt pool W)).E (repeatMaskWeight J (u W) ∅) else 0)) := by
      apply expect_le
      intro W
      apply expect_le
      intro pool
      by_cases ht : F.typical C pool
      · simpa only [if_pos ht] using query_mask_expansion (FinLaw.pi (Qt pool W)) (u W) (hu W)
      · simp [ht]
    _ = ∑ J : Fin q → Bool, H.E (fun W => PoolLaw.E (fun pool => if F.typical C pool then
        (FinLaw.pi (Qt pool W)).E (repeatMaskWeight J (u W) ∅) else 0)) := by
      simp_rw [expect_sum]
    _ ≤ ∑ J : Fin q → Bool, (c ^ q * s ^ q) * (δ ^ maskDrops J * ∏ a, if J a then 1 else μ a) :=
      Finset.sum_le_sum (fun J _ => hJ J)
    _ = _ := by rw [← Finset.mul_sum, sum_masks]

end HypercubeRamsey.S18.Lane_sol_d18l_cal
