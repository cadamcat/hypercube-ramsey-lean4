import HypercubeRamsey.S18.ProducerInputs

namespace HypercubeRamsey.S18

open Classical Filter
open S16 S16.Lane_sol_fix2_s16

private structure DiagnosticAt {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {R : CellRawData G}
    {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm) (C : G.Cell) (c0 : ℝ) where
  Check : Type
  [checkFin : Fintype Check]
  diagnostic : CellPoolDiagnostics (Fin (G.nslot C))
    (Bin PT.tiling (G.cellPatch C)) (R.Hist C) Check (T.S.n k) c0
  linked : CellDiagnosticLink K C diagnostic
  concentration : PoolConcentrationHypotheses diagnostic
  load : LoadGateHypotheses diagnostic

attribute [instance] DiagnosticAt.checkFin

/-- The physical Section 16 handoff (16:147–482). The raw source, permission
table, diagnostics, calibrated stages and fresh readout all refer to the same
geometry and kernels. Typicality has positive mass under the diagnostic's
uniform iid-slot law, and the state specification uses the actual internal
probability-prior predicate rather than an arbitrary validity predicate. -/
structure PhysicalFreshCertificate {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) (F : FreshCell G) where
  admissible : κ.Admissible
  K16 : ℝ
  quantitative : LowModeQuantFacts admissible (PT := PT) K16
  geometry : LowGeometryCertificate admissible quantitative
  geometry_eq : geometry.geom = G
  uniform : SolverLabelsUniform PT
  scale : CellCalibrationScale PT
  raw : CellRawData G
  source_valid : raw.SourceValid
  permissions : CellPermissions raw
  permission_loss : ∀ C W, (raw.history C).w W ≠ 0 →
    PermissionLossHypotheses (permissions.table C) (raw.qin C W)
  kernels : CellRestrictedKernels raw permissions
  c0 : ℝ
  diagnostics : CellDiagnostics kernels c0
  stages : CellCalibratedStages kernels
  typical_eq : ∀ C pool, stages.typical C pool ↔ (diagnostics.diagnostic C).typical pool
  gate_eq : ∀ C pool,
    stages.gate C pool = Finset.univ.filter ((diagnostics.diagnostic C).loadGate pool)
  calibration : FreshLabelCalibration F
  construction : FreshConstructionLink stages F calibration
  fresh_spec : FreshCell.Spec F (InternallyValid F calibration) calibration.permittedLabels
  typical_failure : ∀ C,
    (diagnostics.diagnostic C).poolLaw.pr (fun pool => ¬ F.typical C pool) ≤
      Real.exp (-(T.S.n k : ℝ) ^ c0) / 2
  typical_positive : ∀ C,
    0 < ∑ pool ∈ Finset.univ.filter (F.typical C), (diagnostics.diagnostic C).poolLaw.w pool

/-- The exact raw → permission → restricted diagnostic → calibrated stage
→ fresh validity chain. All linked data are built using S16 exports. The
cutoff is selected before every stage, cell and profile. -/
theorem fresh_cell_from_exports {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage}, DeepDisc T κ.xs κ.α 0.04 →
      ∀ {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
        (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q),
        SolverLabelsUniform PT → CellCalibrationScale PT → n₀ ≤ T.S.n k →
        TwoBudgetDisc T k ((T.S.n k : ℝ) ^ κ.xs) (κ.α * T.S.n k)
          ((T.S.n k : ℝ) ^ (-1 + (0.04 : ℝ))) →
        ∃ F : FreshCell H.geom, Nonempty (PhysicalFreshCertificate H.geom F) := by
  obtain ⟨nr, hr⟩ := cell_raw_data_exists hκ
  obtain ⟨np, hp⟩ := cell_permission_hypotheses hκ
  obtain ⟨nd, c0, hc0, hd⟩ := cell_pool_diagnostics_exists hκ
  obtain ⟨ns, hs⟩ := cell_calibrated_stages_exists hκ
  obtain ⟨nf, hf⟩ := fresh_cell_spec_exists hκ
  refine ⟨max nr (max np (max nd (max ns nf))), ?_⟩
  intro T hDisc k PT K16 Q H hU hCal hn hAt
  obtain ⟨R, hR⟩ := hr Q H hU (by omega)
  obtain ⟨Perm, hPerm⟩ := hp hDisc Q H R hR (by omega) hAt
  obtain ⟨K, hK⟩ := hd Q H R Perm hR (by omega) hPerm
  have hDiag : ∀ C, Nonempty (DiagnosticAt K C c0) := by
    intro C
    obtain ⟨Check, checkFin, D, ⟨link⟩, ⟨conc⟩, ⟨load⟩⟩ := hK C
    exact ⟨{
      Check := Check
      checkFin := checkFin
      diagnostic := D
      linked := link
      concentration := conc
      load := load }⟩
  let chosen C := Classical.choice (hDiag C)
  let Ds : CellDiagnostics K c0 := {
    exponent_half := hc0
    Check := fun C => (chosen C).Check
    checkFin := fun C => (chosen C).checkFin
    diagnostic := fun C => (chosen C).diagnostic
    linked := fun C => (chosen C).linked
    concentration := fun C => (chosen C).concentration
    load := fun C => (chosen C).load }
  obtain ⟨S, hTypical, hGate⟩ := hs Q H hCal R Perm K Ds hR (by omega) hPerm
  obtain ⟨F, Cal, ⟨link⟩, hSpec⟩ :=
    hf Q H hCal R Perm K Ds S hR (by omega) hPerm hTypical hGate
  have hFailure : ∀ C,
      (Ds.diagnostic C).poolLaw.pr (fun pool => ¬ F.typical C pool) ≤
        Real.exp (-(T.S.n k : ℝ) ^ c0) / 2 := by
    intro C
    simpa only [link.typical_eq, hTypical] using
      (pool_typicality_concentration_after_permission (Ds.diagnostic C) (Ds.concentration C)).1
  refine ⟨F, ⟨{
    admissible := hκ
    K16 := K16
    quantitative := Q
    geometry := H
    geometry_eq := rfl
    uniform := hU
    scale := hCal
    raw := R
    source_valid := hR
    permissions := Perm
    permission_loss := hPerm
    kernels := K
    c0 := c0
    diagnostics := Ds
    stages := S
    typical_eq := hTypical
    gate_eq := hGate
    calibration := Cal
    construction := link
    fresh_spec := hSpec
    typical_failure := hFailure
    typical_positive := ?_ }⟩⟩
  intro C
  have hsum : (∑ pool ∈ Finset.univ.filter (F.typical C), (Ds.diagnostic C).poolLaw.w pool) +
      (Ds.diagnostic C).poolLaw.pr (fun pool => ¬ F.typical C pool) = 1 := by
    rw [Finset.sum_filter, FinLaw.pr, ← Finset.sum_add_distrib]
    calc
      _ = ∑ pool, (Ds.diagnostic C).poolLaw.w pool := by
        apply Finset.sum_congr rfl
        intro pool _
        by_cases ht : F.typical C pool <;> simp [ht]
      _ = 1 := (Ds.diagnostic C).poolLaw.sum_one
  have hexp : Real.exp (-(T.S.n k : ℝ) ^ c0) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  linarith [hFailure C]

end HypercubeRamsey.S18
