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
        ∃ F : FreshCell H.geom, ∃ validState permittedLabels,
          FreshCell.Spec F validState permittedLabels := by
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
  obtain ⟨F, Cal, _link, hSpec⟩ :=
    hf Q H hCal R Perm K Ds S hR (by omega) hPerm hTypical hGate
  exact ⟨F, InternallyValid F Cal, Cal.permittedLabels, hSpec⟩

end HypercubeRamsey.S18
