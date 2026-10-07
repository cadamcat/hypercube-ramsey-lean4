import HypercubeRamsey.S18.Needs
import HypercubeRamsey.S17.Defs

namespace HypercubeRamsey.S18.Lane_q_s18_dl

open Filter
open S16 S16.Lane_sol_fix2_s16

noncomputable def listGateContext {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) (hLow : PT.tiling.mode.isLow)
    (G : LowGeom PT) (F : FreshCell G) (hL16 : L16QuantitativeValidity G F) :
    ListGateContext κ T k PT := by
  let physical := Classical.choice hL16.physical
  exact {
    tiling_valid := hPT
    mode_low := hLow
    G := G
    F := F
    stateValid := fun C pool s => InternallyValid F physical.calibration C pool s
    permittedLabels := physical.calibration.permittedLabels
    slotFactor := fun b =>
      (Fintype.card (Bin PT.tiling (G.patchOf b)) : ℝ) / (G.nslot (G.cellOf b) : ℝ)
    fresh_spec := physical.fresh_spec }

theorem canonical_physical_fresh {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (hDisc : DeepDisc T κ.xs κ.α 0.04) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k), PT.Valid →
      PT.tiling.mode.isLow →
      (∃ G : LowGeom PT, ∃ F : FreshCell G, L16QuantitativeValidity G F) →
      ∃ G : LowGeom PT, ∃ F : FreshCell G, L16QuantitativeValidity G F := by
  obtain ⟨K16, hQuant⟩ := low_mode_quantitative_inputs hκ T
  obtain ⟨nGeom, CGeom, hCGeom, hScale⟩ := S16.low_geometry_thresholds hκ
  obtain ⟨nFresh, hFresh⟩ := fresh_cell_from_exports hκ
  have hNGeom : ∀ᶠ k : ℕ in atTop, nGeom ≤ T.S.n k :=
    T.S.n_tendsto.eventually_ge_atTop nGeom
  have hNFresh : ∀ᶠ k : ℕ in atTop, nFresh ≤ T.S.n k :=
    T.S.n_tendsto.eventually_ge_atTop nFresh
  have hHost : ∀ᶠ k : ℕ in atTop,
      CGeom * (2 : ℝ) ^ T.S.n k ≤ (T.S.N k : ℝ) := by
    filter_upwards [T.S.ratio_tendsto.eventually_ge_atTop CGeom] with k hk
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ T.S.n k)).mp hk
  filter_upwards [hQuant, hNGeom, hNFresh, hHost, hDisc] with k hQuantK hNGeomK hNFreshK hHostK hDiscK
  intro PT hPT hLow hOld
  obtain ⟨G₀, F₀, hL16₀⟩ := hOld
  obtain ⟨physical₀⟩ := hL16₀.physical
  obtain ⟨Q, hGain⟩ := hQuantK PT hPT hLow
  have hScaleK := hScale Q hNGeomK hHostK
  obtain ⟨H⟩ := S16.low_geometry_at_scale hκ Q hScaleK
  obtain ⟨F, hPhysical⟩ := hFresh hDisc Q H physical₀.uniform physical₀.scale hNFreshK hDiscK
  exact ⟨H.geom, F, l16_validity_of_certificate hκ Q H hGain F hPhysical⟩

end HypercubeRamsey.S18.Lane_q_s18_dl
